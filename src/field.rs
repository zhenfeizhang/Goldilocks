//! This module defines our customized field trait.

use ff::PrimeField;
use serde::Serialize;

use crate::{fp2::GoldilocksExt2, Goldilocks, GoldilocksExt3};

pub trait SmallField: PrimeField + Serialize {
    const NAME: &'static str;
}

impl SmallField for Goldilocks {
    const NAME: &'static str = "Goldilocks";
}
impl SmallField for GoldilocksExt2 {
    const NAME: &'static str = "GoldilocksExt2";
}
impl SmallField for GoldilocksExt3 {
    const NAME: &'static str = "GoldilocksExt3";
}
