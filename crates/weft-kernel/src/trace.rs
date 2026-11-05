use crate::{invalid, replay};
use weft_domain::{Diagnostic, NodeValue};

pub(crate) fn record_premises(
    values: &[NodeValue],
    premises: &[usize],
    row: usize,
    words: &mut [u64],
) -> Result<bool, Diagnostic> {
    let start = row
        .checked_mul(premises.len())
        .ok_or_else(|| invalid("Premise trace offset overflow"))?;
    let mut holds = true;
    for (index, position) in premises.iter().enumerate() {
        let value = replay::at(values, *position)?;
        holds &= value;
        let bit = start
            .checked_add(index)
            .ok_or_else(|| invalid("Premise trace bit overflow"))?;
        let word = words
            .get_mut(bit / 64)
            .ok_or_else(|| invalid("Missing premise trace word"))?;
        let mask = 1_u64 << (bit % 64);
        if value {
            *word |= mask;
        } else {
            *word &= !mask;
        }
    }
    Ok(holds)
}
