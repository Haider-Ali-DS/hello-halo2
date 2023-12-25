use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner},
    pasta::{EqAffine, Fp},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Instance, Selector, SingleVerifier,
    },
    poly::{commitment::Params, Rotation},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand::rngs::OsRng;

// x * 3 + x + 5 = 35
// x2 = x * x
// x3 = x2 * x
// x3_x = x3 + x
// x3_x_5 = x3_x + 5
// x3_x_5 == 35

//instruction set must be implemented by our circuit
trait Ops {
    type Num;
    // Api between your chip with outside
    // layouter helps manage circuit to be more moduler, flexible and help places value to its proper place
    fn load_private(&self, layouter: impl Layouter<Fp>, x: Option<Fp>) -> Result<Self::Num, Error>;
    // this is for constant similar as Api
    fn load_constant(&self, layouter: impl Layouter<Fp>, x: Fp) -> Result<Self::Num, Error>;
    // multiplication on fields,
    fn mul(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    // does addition on fields
    fn add(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    // exposes the public value/result to verify if it matches the end of operation
    fn expose_public(
        &self,
        layouter: impl Layouter<Fp>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

#[derive(Debug)]
struct MyChip {
    config: MyConfig,
}

impl MyChip {
    pub fn new(config: MyConfig) -> Self {
        Self { config }
    }

    fn configure(
        meta: &mut ConstraintSystem<Fp>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<halo2_proofs::plonk::Fixed>,
    ) -> MyConfig {
        meta.enable_constant(constant);
        meta.enable_equality(instance);
        for adv in advice.iter() {
            meta.enable_equality(*adv);
        }
        let s_mul = meta.selector();
        let s_add = meta.selector();
        meta.create_gate("mul/add", |meta| {
            // lhs, advice column for first row
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            // rhs. advice column for first row
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            // output is first column for next row
            let out = meta.query_advice(advice[0], Rotation::next());
            // pickup the selectors to add these columns
            let s_mul = meta.query_selector(s_mul);
            let s_add = meta.query_selector(s_add);
            // condition for gate is
            // if s_mul == 0 then first condition is nothing
            // if its 1 then the next value (lhs * rhs - out) must be 0
            // similar with add so both of the values should be 0 as a constraint
            // either through selector or the operation
            // we enable s_mul in add/mul function of circuit using config.s_mul.enable(region, row);
            // if both are 0 or off we dont care about the value then
            vec![
                s_mul * (lhs.clone() * rhs.clone() - out.clone()),
                s_add * (lhs + rhs - out),
            ]
        });

        MyConfig {
            advice,
            instance,
            s_mul,
            s_add,
        }
    }
}

impl Chip<Fp> for MyChip {
    type Config = MyConfig;

    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Ops for MyChip {
    type Num = AssignedCell<Fp, Fp>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<Fp>,
        v: Option<Fp>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        // region basically eccompasses a set of cells it can be multiple cells or even multiple rows,
        // region helps organize the circuit into logical sections
        layouter.assign_region(
            // naming helps in debugging purposes when something goes wrong
            || "load private",
            |mut region| {
                region.assign_advice(
                    || "private value",
                    config.advice[0],
                    0,
                    || v.ok_or(Error::Synthesis),
                )
            },
        )
    }

    fn load_constant(&self, mut layouter: impl Layouter<Fp>, v: Fp) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "load constant",
            |mut region| region.assign_advice_from_constant(|| "constant", config.advice[0], 0, v),
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "mul",
            |mut region| {
                // offset here is the row, and config.advice[0]/1 == column
                // so we just multiply in the matrix or telling layouter which portion
                // of circuit has to be taken and which value you want them to have or what relation you want between them
                // and then store the value in row 1 with column 0 value in assign_advice
                config.s_mul.enable(&mut region, 0)?;
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                let v = a.value().and_then(|a| b.value().map(|b| *a * *b));
                region.assign_advice(
                    || "a * b",
                    config.advice[0],
                    1,
                    || v.ok_or(Error::Synthesis),
                )
            },
        )
    }

    fn add(
        &self,
        mut layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        // this is config of the circuit not the chip
        let config = self.config();
        layouter.assign_region(
            || "add",
            |mut region| {
                config.s_add.enable(&mut region, 0)?;
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                // this is the basic operation
                let v = a.value().and_then(|a| b.value().map(|b| *a + *b));
                // this basically assigns value to the region
                region.assign_advice(
                    || "a + b",
                    config.advice[0],
                    1,
                    || v.ok_or(Error::Synthesis),
                )
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<Fp>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.cell(), config.instance, row)
    }
}

#[derive(Clone, Debug)]
struct MyConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    // selectors to define the rule of we want multiplication selector or addition selector
    s_mul: Selector,
    s_add: Selector,
}

#[derive(Default)]
struct MyCircuit {
    constant: Fp,
    x: Option<Fp>,
}

impl Circuit<Fp> for MyCircuit {
    type Config = MyConfig;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // these are input pins for the circuit,
    // advice is private value to,
    // one column for to store parameter,
    // one column to use prefix constant
    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        MyChip::configure(meta, advice, instance, constant)
    }

    // so circuit uses chip, and perform basic operations,
    // so we chain things together to get our desired result here.
    // below is basic instruction being used in the circuit
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2_proofs::circuit::Layouter<Fp>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let chip = MyChip::new(config);
        let x = chip.load_private(layouter.namespace(|| "load x"), self.x)?;
        let constant = chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let x_2 = chip.mul(layouter.namespace(|| "x2"), x.clone(), x.clone())?;
        let x_3 = chip.mul(layouter.namespace(|| "x3"), x_2, x.clone())?;
        let x_3_x = chip.add(layouter.namespace(|| "x3_x"), x_3, x)?;
        let x_3_x_5 = chip.add(layouter.namespace(|| "x3_x_5"), x_3_x, constant)?;
        chip.expose_public(layouter.namespace(|| "expose res"), x_3_x_5, 0)
    }
}

fn main() {
    //replace this x to fail the circuit since 3 is correct solution for provided circuit
    // Fp: F is integer in field and p is size of the field which is very large,
    // x is advice, which we are keeping as secret, all other built on it are also secret
    let x = Fp::from(4);
    //constant in our equation, never changes
    let constant = Fp::from(5);
    // Rhs of the equation, Instant variable, public parameter
    let result = Fp::from(35);

    // our circuit
    // very mathematical in nature
    let circuit = MyCircuit {
        constant,
        x: Some(x),
    };

    ////// basic run
    // our public inputs which are available to everyone
    // let public_inputs = vec![result];

    // Mock Prover of same idea as prover
    // let prover = MockProver::run(4, &circuit, vec![public_inputs]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));

    /////// draw circuit plot
    // use plotters::prelude::*;
    // let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    // root.fill(&WHITE).unwrap();
    // let root = root
    //     .titled("Example Circuit Layout", ("sans-serif", 60))
    //     .unwrap();

    // halo2_proofs::dev::CircuitLayout::default()
    //     .view_width(0..2)
    //     .view_height(0..16)
    //     .show_labels(false)
    //     .render(5, &circuit, &root)
    //     .unwrap()

    ////// generating verifiable proof

    // parameter to determine the size of circuit, dont put too large number to waste circuit space, and too small would lead to not enough space
    let params: Params<EqAffine> = Params::new(4);
    // generates verification key
    let vk = keygen_vk(&params, &circuit).unwrap();
    // proving key based on circuit
    let pk = keygen_pk(&params, vk, &circuit).unwrap();
    //output file to which proof is written
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    //creates proof and write element of proof in transacript
    create_proof(
        &params,
        &pk,
        &[circuit],
        &[&[&[result]]],
        OsRng,
        &mut transcript,
    )
    .unwrap();

    let proof = transcript.finalize();
    println!("proof length is {:?}", proof.len());

    ////// verification of proof, note we dont have knowledge of circuit below nor do we know x
    // creates a verifier
    let strategy = SingleVerifier::new(&params);
    // creates a reader to read proof
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    //verifies the proof and pass if its ok
    assert!(verify_proof(
        &params,
        pk.get_vk(),
        strategy,
        &[&[&[result]]],
        &mut transcript
    )
    .is_ok());
}
