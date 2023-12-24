use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};

// x * 3 + x + 5 = 35
// x2 = x * x
// x3 = x2 * x
// x3_x = x3 + x
// x3_x_5 = x3_x + 5
// x3_x_5 == 35

trait Ops {
    type Num;
    fn load_private(&self, layouter: impl Layouter<Fp>, x: Option<Fp>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<Fp>, x: Fp) -> Result<Self::Num, Error>;
    fn mul(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn add(
        &self,
        layouter: impl Layouter<Fp>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
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
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            let s_add = meta.query_selector(s_add);
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
        layouter.assign_region(
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
        let config = self.config();
        layouter.assign_region(
            || "add",
            |mut region| {
                config.s_add.enable(&mut region, 0)?;
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                let v = a.value().and_then(|a| b.value().map(|b| *a + *b));
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

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<Fp>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        MyChip::configure(meta, advice, instance, constant)
    }

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
    let x = Fp::from(3);
    let constant = Fp::from(5);
    let result = Fp::from(35);

    let circuit = MyCircuit {
        constant,
        x: Some(x),
    };
    let public_inputs = vec![result];

    let prover = MockProver::run(4, &circuit, vec![public_inputs]).unwrap();

    assert_eq!(prover.verify(), Ok(()));
}
