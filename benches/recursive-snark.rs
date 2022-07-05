#![allow(non_snake_case)]

extern crate flate2;

use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  traits::{Group, StepCircuit},
  PublicParams, RecursiveSNARK,
};

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

use bellperson::{
  gadgets::{num::AllocatedNum, Assignment},
  ConstraintSystem, SynthesisError,
};
use criterion::*;
use ff::PrimeField;
use rand::rngs::OsRng;
use std::time::Duration;

fn recursive_snark_benchmark(c: &mut Criterion) {
  let num_samples = 10;
  let num_cons_ver_circuit = 20584;
  // First run for 0 constraints
  for num_steps in 10..30 {
    bench_recursive_snark(c, num_samples, num_steps, 0);
  }
  for &log_num_cons in [15, 16, 17, 18, 19, 20].iter() {
    for num_steps in 10..30 {
      let num_cons = usize::pow(2, log_num_cons) - num_cons_ver_circuit;
      bench_recursive_snark(c, num_samples, num_steps, num_cons);
    }
  }
}

fn set_duration() -> Criterion {
  Criterion::default().warm_up_time(Duration::from_millis(3000))
}

criterion_group! {
name = recursive_snark;
config = set_duration();
targets = recursive_snark_benchmark
}

criterion_main!(recursive_snark);

fn bench_recursive_snark(c: &mut Criterion, num_samples: usize, num_steps: usize, num_cons: usize) {
  let name = format!("RecursiveSNARK-NumCons-{}-NumSteps-{}", num_cons, num_steps);
  let mut group = c.benchmark_group(name.clone());
  group.sample_size(num_samples);
  // Produce public parameters
  let pp = PublicParams::<
    G1,
    G2,
    TestCircuit<<G1 as Group>::Scalar>,
    TestCircuit<<G2 as Group>::Scalar>,
  >::setup(TestCircuit::new(0), TestCircuit::new(num_cons));
  // Bench time to produce a recursive SNARK
  group.bench_function("Prove", |b| {
    b.iter(|| {
      // produce a recursive SNARK
      assert!(RecursiveSNARK::prove(
        black_box(&pp),
        black_box(num_steps),
        black_box(<G1 as Group>::Scalar::zero()),
        black_box(<G2 as Group>::Scalar::zero()),
      )
      .is_ok());
    })
  });
  let res = RecursiveSNARK::prove(
    &pp,
    num_steps,
    <G1 as Group>::Scalar::zero(),
    <G2 as Group>::Scalar::zero(),
  );
  assert!(res.is_ok());
  let recursive_snark = res.unwrap();

  // verify the recursive SNARK
  let res = recursive_snark.verify(
    &pp,
    num_steps,
    <G1 as Group>::Scalar::zero(),
    <G2 as Group>::Scalar::zero(),
  );
  assert!(res.is_ok());
  // Output the proof size
  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, &recursive_snark.serialize()).unwrap();
  let proof_encoded = encoder.finish().unwrap();
  println!("{}/ProofSize: {} B", name, proof_encoded.len(),);

  // Benchmark the verification time
  let name = "Verify";
  group.bench_function(name, |b| {
    b.iter(|| {
      assert!(black_box(&recursive_snark)
        .verify(
          black_box(&pp),
          black_box(num_steps),
          black_box(<G1 as Group>::Scalar::zero()),
          black_box(<G2 as Group>::Scalar::zero()),
        )
        .is_ok());
    });
  });
  group.finish();
}

// The test circuit has $num_cons constraints. each constraint i is of the form
// (a*x_{i-1} + 1) * b = x_i
// where a and b are random coefficients. x_{-1} = input z and x_n is the output z
#[derive(Clone, Debug)]
struct TestCircuit<F: PrimeField> {
  num_cons: usize,
  coeffs: Vec<(F, F)>,
}

impl<F> TestCircuit<F>
where
  F: PrimeField,
{
  pub fn new(num_cons: usize) -> Self {
    // Generate 2*num_cons random field elements (each constraint has two coefficients
    let coeffs = (0..num_cons)
      .map(|_| (F::random(&mut OsRng), F::random(&mut OsRng)))
      .collect();
    Self { num_cons, coeffs }
  }
}

impl<F> StepCircuit<F> for TestCircuit<F>
where
  F: PrimeField,
{
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: AllocatedNum<F>,
  ) -> Result<AllocatedNum<F>, SynthesisError> {
    let mut output = z;
    for i in 0..self.num_cons {
      let a = self.coeffs[i].0;
      let b = self.coeffs[i].1;
      let z_new = AllocatedNum::alloc(cs.namespace(|| format!("alloc x_{}", i)), || {
        Ok((*output.get_value().get()? * a + F::one()) * b)
      })?;
      cs.enforce(
        || format!("Constraint {}", i),
        |lc| lc + (a, output.get_variable()) + CS::one(),
        |lc| lc + (b, CS::one()),
        |lc| lc + z_new.get_variable(),
      );
      output = z_new
    }
    Ok(output)
  }

  fn compute(&self, z: &F) -> F {
    let mut output = *z;
    for i in 0..self.num_cons {
      output = (output * self.coeffs[i].0 + F::one()) * self.coeffs[i].1
    }
    output
  }
}
