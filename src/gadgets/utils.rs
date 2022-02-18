use bellperson::{
  gadgets::{
    boolean::AllocatedBit, 
    num::AllocatedNum,
    Assignment,
  },
  ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};

///Gets as input the little indian representation of a number and spits out the number
#[allow(dead_code)]
pub fn le_bits_to_num<Scalar, CS>(
  mut cs: CS,
  bits: Vec<AllocatedBit>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
  Scalar: PrimeField + PrimeFieldBits,
  CS: ConstraintSystem<Scalar>,
{
  //We loop over the input bits and construct the constraint and the field element that corresponds
  //to the result
  let mut lc = LinearCombination::zero();
  let mut coeff = Scalar::one();
  let mut fe = Some(Scalar::zero());
  for bit in bits.iter() {
    lc = lc + (coeff, bit.get_variable());
    fe = bit.get_value().map(|val| {
      if val {
        fe.unwrap() + coeff
      } else {
        fe.unwrap()
      }
    });
    coeff = coeff.double();
  }
  let num = AllocatedNum::alloc(cs.namespace(|| "Field element"), || {
    fe.ok_or(SynthesisError::AssignmentMissing)
  })?;
  lc = lc - num.get_variable();
  cs.enforce(|| "compute number from bits", |lc| lc, |lc| lc, |_| lc);
  Ok(num)
}

///Allocate a variable that is set to zero
pub fn alloc_zero<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let zero = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(F::zero()))?;
  cs.enforce(
    || "check zero is valid",
    |lc| lc + zero.get_variable(),
    |lc| lc + zero.get_variable(),
    |lc| lc,
  );
  Ok(zero)
}

///Allocate a variable that is set to one
#[allow(dead_code)]
pub fn alloc_one<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let one = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(F::one()))?;
  cs.enforce(
    || "check one is valid",
    |lc| lc + one.get_variable(),
    |lc| lc + one.get_variable(),
    |lc| lc + CS::one(),
  );

  Ok(one)
}

///Allocate a variable that is set to false
pub fn alloc_false<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedBit, SynthesisError> {
  let false_alloc = AllocatedBit::alloc(cs.namespace(|| "alloc false"), Some(false))?;
  cs.enforce(
    || "check false is valid",
    |lc| lc + false_alloc.get_variable(),
    |lc| lc + false_alloc.get_variable(),
    |lc| lc,
  );

  Ok(false_alloc)
}

///Allocate a variable that is set to true
pub fn alloc_true<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedBit, SynthesisError> {
  let true_alloc = AllocatedBit::alloc(cs.namespace(|| "alloc true"), Some(true))?;
  cs.enforce(
    || "check true is valid",
    |lc| lc + true_alloc.get_variable(),
    |lc| lc + true_alloc.get_variable(),
    |lc| lc + CS::one(),
  );

  Ok(true_alloc)
}

//The next two functions are borrowed from sapling-crypto crate

///Check that two numbers are equal and return a bit
pub fn alloc_num_equals<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: AllocatedNum<F>,
  b: AllocatedNum<F>,
) -> Result<AllocatedBit, SynthesisError> {
  // Allocate and constrain `r`: result boolean bit.
  // It equals `true` if `a` equals `b`, `false` otherwise

  let r_value = match (a.get_value(), b.get_value()) {
    (Some(a), Some(b)) => Some(a == b),
    _ => None,
  };

  let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

  let delta = AllocatedNum::alloc(cs.namespace(|| "delta"), || {
    let a_value = *a.get_value().get()?;
    let b_value = *b.get_value().get()?;

    let mut delta = a_value;
    delta.sub_assign(&b_value);

    Ok(delta)
  })?;

  //
  cs.enforce(
    || "delta = (a - b)",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + CS::one(),
    |lc| lc + delta.get_variable(),
  );

  let delta_inv = AllocatedNum::alloc(cs.namespace(|| "delta_inv"), || {
    let delta = *delta.get_value().get()?;

    if delta.is_zero().unwrap_u8() == 1 {
      Ok(F::one()) // we can return any number here, it doesn't matter
    } else {
      Ok(delta.invert().unwrap())
    }
  })?;

  // Allocate `t = delta * delta_inv`
  // If `delta` is non-zero (a != b), `t` will equal 1
  // If `delta` is zero (a == b), `t` cannot equal 1

  let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
    let mut tmp = *delta.get_value().get()?;
    tmp.mul_assign(&(*delta_inv.get_value().get()?));

    Ok(tmp)
  })?;

  // Constrain allocation:
  // t = (a - b) * delta_inv
  cs.enforce(
    || "t = (a - b) * delta_inv",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + delta_inv.get_variable(),
    |lc| lc + t.get_variable(),
  );

  // Constrain:
  // (a - b) * (t - 1) == 0
  // This enforces that correct `delta_inv` was provided,
  // and thus `t` is 1 if `(a - b)` is non zero (a != b )
  cs.enforce(
    || "(a - b) * (t - 1) == 0",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + t.get_variable() - CS::one(),
    |lc| lc,
  );

  // Constrain:
  // (a - b) * r == 0
  // This enforces that `r` is zero if `(a - b)` is non-zero (a != b)
  cs.enforce(
    || "(a - b) * r == 0",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + r.get_variable(),
    |lc| lc,
  );

  // Constrain:
  // (t - 1) * (r - 1) == 0
  // This enforces that `r` is one if `t` is not one (a == b)
  cs.enforce(
    || "(t - 1) * (r - 1) == 0",
    |lc| lc + t.get_variable() - CS::one(),
    |lc| lc + r.get_variable() - CS::one(),
    |lc| lc,
  );

  Ok(r)
}

///If condition return a otherwise b
pub fn conditionally_select<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  condition: &AllocatedBit,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if condition.get_value().is_some() && condition.get_value().unwrap() {
      Ok(*a.get_value().get()?)
    } else {
      Ok(*b.get_value().get()?)
    }
  })?;

  // a * condition + b*(1-condition) = c ->
  // a * condition - b*condition = c - b

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + condition.get_variable(),
    |lc| lc + c.get_variable() - b.get_variable(),
  );

  Ok(c)
}

///If condition return a otherwise b for a and b bits
///Returns true if (a AND b) or (cond AND a) or cond AND b
pub fn conditionally_select_bit<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedBit,
  b: &AllocatedBit,
  condition: &AllocatedBit,
) -> Result<AllocatedBit, SynthesisError> {
  let c = AllocatedBit::alloc(cs.namespace(|| "conditional select result"), {
    if condition.get_value().is_some() && condition.get_value().unwrap() {
      a.get_value()
    } else {
      b.get_value()
    }
  })?;

  // a * condition + b*(1-condition) = c ->
  // a * condition - b*condition = c - b

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + condition.get_variable(),
    |lc| lc + c.get_variable() - b.get_variable(),
  );

  Ok(c)
}

///Same as the above but Condition is an AllocatedNum that needs to be
///0 or 1. 1 => True, 0 => False
#[allow(dead_code)]
pub fn conditionally_select2<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  condition: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if *condition.get_value().get()? == F::one() {
      Ok(*a.get_value().get()?)
    } else {
      Ok(*b.get_value().get()?)
    }
  })?;

  // a * condition + b*(1-condition) = c ->
  // a * condition - b*condition = c - b

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable() - b.get_variable(),
    |lc| lc + condition.get_variable(),
    |lc| lc + c.get_variable() - b.get_variable(),
  );

  Ok(c)
}

///If condition set to 0 otherwise a
pub fn select_zero_or<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  condition: &AllocatedBit,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if condition.get_value().is_none() || condition.get_value().unwrap() {
      Ok(F::zero())
    } else {
      Ok(*a.get_value().get()?)
    }
  })?;

  // a * (1 - condition) = c

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable(),
    |lc| lc + CS::one() - condition.get_variable(),
    |lc| lc + c.get_variable(),
  );

  Ok(c)
}

///If condition set to 1 otherwise a
pub fn select_one_or<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  condition: &AllocatedBit,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if condition.get_value().is_none() || condition.get_value().unwrap() {
      Ok(F::one())
    } else {
      Ok(*a.get_value().get()?)
    }
  })?;

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + CS::one() - a.get_variable(),
    |lc| lc + condition.get_variable(),
    |lc| lc + c.get_variable() - a.get_variable(),
  );
  Ok(c)
}

///If condition set to a otherwise 1
pub fn select_variable_or_one<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  condition: &AllocatedBit,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if condition.get_value().is_some() && condition.get_value().unwrap() {
      Ok(*a.get_value().get()?)
    } else {
      Ok(F::one())
    }
  })?;

  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable() - CS::one(),
    |lc| lc + condition.get_variable(),
    |lc| lc + c.get_variable() - CS::one(),
  );
  Ok(c)
}

pub fn bit_to_num<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bit: AllocatedBit
) -> Result<AllocatedNum<F>, SynthesisError> {
    let num = AllocatedNum::alloc(
        cs.namespace(|| "allocate bit from num"),
        || {
            if bit.get_value().is_some() && bit.get_value().unwrap() {
                Ok(F::one())
            }else{
                Ok(F::zero())
            }
        }
    )?;

    cs.enforce(
        || "convert num to bit" ,
        |lc| lc,
        |lc| lc,
        |lc| lc + bit.get_variable() - num.get_variable(),
    );

    Ok(num)
}
