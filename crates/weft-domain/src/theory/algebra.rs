//! Native set algebra over materialized finite sets: union, intersection,
//! left difference, typed membership and inclusive subset.
//!
//! Every operation charges both complete operand traversals (members and
//! origins) plus one operator charge before any filtering, then materializes
//! through the single `add_set` normalization path — the same path spreads
//! and literals use. Results keep deterministic first-occurrence order: union
//! keeps left order then unseen right members; intersection and difference
//! keep qualifying left order. Eliminated members stay reachable through the
//! operation origin, which links both whole operand sets.

use crate::{
    InvariantError, OriginKind, ScalarType, SetId, SetMember, SetOperation, SourceSpan,
    TheoryBuilder, ValueId,
};
use std::collections::{HashMap, HashSet};

impl TheoryBuilder {
    fn operand_members(
        &self,
        id: SetId,
        label: &'static str,
    ) -> Result<(Vec<SetMember>, Option<ScalarType>, crate::OriginId), InvariantError> {
        let set = self
            .set(id)
            .ok_or(InvariantError::InvalidReference(label))?;
        Ok((set.members.clone(), set.element_type.clone(), set.origin))
    }

    fn charge_operands(&mut self, left: SetId, right: SetId) -> Result<(), InvariantError> {
        let (a, ..) = self.operand_members(left, "left set")?;
        let (b, ..) = self.operand_members(right, "right set")?;
        let work = a.len().saturating_add(b.len()).saturating_add(1);
        self.charge(work)
    }

    fn unified_element_type(
        &self,
        left: SetId,
        right: SetId,
    ) -> Result<Option<ScalarType>, InvariantError> {
        let a = self
            .set(left)
            .ok_or(InvariantError::InvalidReference("left set"))?;
        let b = self
            .set(right)
            .ok_or(InvariantError::InvalidReference("right set"))?;
        match (&a.element_type, &b.element_type) {
            (Some(x), Some(y)) if x != y => Err(InvariantError::MixedSetTypes),
            (x, y) => Ok(x.clone().or(y.clone())),
        }
    }

    fn operation_origin(
        &mut self,
        operation: SetOperation,
        left: SetId,
        right: SetId,
        left_origin: crate::OriginId,
        right_origin: crate::OriginId,
        span: SourceSpan,
    ) -> Result<crate::OriginId, InvariantError> {
        self.add_origin(
            OriginKind::SetOperation {
                operation,
                left,
                right,
            },
            span,
            vec![left_origin, right_origin],
        )
    }

    /// Union: both normalized operand lists, left order first. `add_set`
    /// deduplicates with first occurrence and merges origins.
    pub fn set_union(
        &mut self,
        left: SetId,
        right: SetId,
        span: SourceSpan,
    ) -> Result<SetId, InvariantError> {
        self.charge_operands(left, right)?;
        let ty = self.unified_element_type(left, right)?;
        let (a, _, a_origin) = self.operand_members(left, "left set")?;
        let (b, _, b_origin) = self.operand_members(right, "right set")?;
        let operation =
            self.operation_origin(SetOperation::Union, left, right, a_origin, b_origin, span)?;
        let mut raw = Vec::with_capacity(a.len() + b.len());
        for source in a.iter().chain(b.iter()) {
            let origin =
                self.add_origin(OriginKind::SetMember, span, vec![operation, source.origin])?;
            raw.push(SetMember {
                value: source.value,
                origin,
            });
        }
        self.add_set(ty, raw, span, vec![operation])
    }

    /// Intersection: each qualifying left member once, in left order, with
    /// the contributing origins of every matching right alias merged in.
    pub fn set_intersection(
        &mut self,
        left: SetId,
        right: SetId,
        span: SourceSpan,
    ) -> Result<SetId, InvariantError> {
        self.charge_operands(left, right)?;
        let ty = self.unified_element_type(left, right)?;
        let (a, _, a_origin) = self.operand_members(left, "left set")?;
        let (b, _, b_origin) = self.operand_members(right, "right set")?;
        let right_members: HashMap<ValueId, SetMember> = b
            .iter()
            .copied()
            .map(|member| (member.value, member))
            .collect();
        let operation = self.operation_origin(
            SetOperation::Intersection,
            left,
            right,
            a_origin,
            b_origin,
            span,
        )?;
        let mut raw = Vec::new();
        for source in &a {
            if let Some(matching) = right_members.get(&source.value) {
                let origin = self.add_origin(
                    OriginKind::SetMember,
                    span,
                    vec![operation, source.origin, matching.origin],
                )?;
                raw.push(SetMember {
                    value: source.value,
                    origin,
                });
            }
        }
        self.add_set(ty, raw, span, vec![operation])
    }

    /// Left difference: surviving left members in left order with their own
    /// origins; the entire right operand stays linked at operation level.
    pub fn set_difference(
        &mut self,
        left: SetId,
        right: SetId,
        span: SourceSpan,
    ) -> Result<SetId, InvariantError> {
        self.charge_operands(left, right)?;
        let ty = self.unified_element_type(left, right)?;
        let (a, _, a_origin) = self.operand_members(left, "left set")?;
        let (b, _, b_origin) = self.operand_members(right, "right set")?;
        let removed: HashSet<ValueId> = b.iter().map(|member| member.value).collect();
        let operation = self.operation_origin(
            SetOperation::Difference,
            left,
            right,
            a_origin,
            b_origin,
            span,
        )?;
        let mut raw = Vec::new();
        for source in &a {
            if !removed.contains(&source.value) {
                let origin =
                    self.add_origin(OriginKind::SetMember, span, vec![operation, source.origin])?;
                raw.push(SetMember {
                    value: source.value,
                    origin,
                });
            }
        }
        self.add_set(ty, raw, span, vec![operation])
    }

    /// Typed membership probe: the scalar's type must match the set's
    /// element type when both are known; the whole set is charged.
    pub fn set_member(&mut self, value: ValueId, set: SetId) -> Result<bool, InvariantError> {
        let members = {
            let target = self
                .set(set)
                .ok_or(InvariantError::InvalidReference("membership set"))?;
            target.members.clone()
        };
        self.charge(members.len().saturating_add(1))?;
        let scalar = self
            .value(value)
            .ok_or(InvariantError::InvalidReference("probe value"))?;
        let element_type = self
            .set(set)
            .ok_or(InvariantError::InvalidReference("membership set"))?
            .element_type
            .clone();
        if let Some(ty) = element_type
            && !scalar.has_type(&ty)
        {
            return Err(InvariantError::MixedSetTypes);
        }
        Ok(members.iter().any(|member| member.value == value))
    }

    /// Inclusive subset over both whole sets. Returns the deterministic
    /// first-left counterexample member when the subset does not hold.
    pub fn set_subset(
        &mut self,
        left: SetId,
        right: SetId,
    ) -> Result<(bool, Option<SetMember>), InvariantError> {
        self.charge_operands(left, right)?;
        let ty = self.unified_element_type(left, right)?;
        let _ = ty;
        let (a, ..) = self.operand_members(left, "left set")?;
        let (b, ..) = self.operand_members(right, "right set")?;
        let right_values: HashSet<ValueId> = b.iter().map(|member| member.value).collect();
        for member in &a {
            if !right_values.contains(&member.value) {
                return Ok((false, Some(*member)));
            }
        }
        Ok((true, None))
    }
}
