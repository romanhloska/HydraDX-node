//! Tests for the HydraDX Runtime Configuration

use crate::*;
use frame_support::weights::{DispatchClass, WeightToFeePolynomial};
use pallet_transaction_payment::Multiplier;
use sp_runtime::traits::Convert;
use sp_runtime::FixedPointNumber;

#[test]
fn full_block_cost() {
	let max_bytes = *BlockLength::get().max.get(DispatchClass::Normal) as u128;
	let length_fee = max_bytes * TransactionByteFee::get();
	assert_eq!(length_fee, 3_932_160_000_000_000);

	let max_weight = BlockWeights::get().get(DispatchClass::Normal).max_total.unwrap_or(1);
	let weight_fee = WeightToFee::calc(&max_weight);
	assert_eq!(weight_fee, 120000000000000);

	let target_fee = 4052160125000000;
	assert_eq!(ExtrinsicBaseWeight::get() as u128 + length_fee + weight_fee, target_fee);
}

#[test]
// This function tests that the fee for `ExtrinsicBaseWeight` of weight is correct
fn extrinsic_base_fee_is_correct() {
	// `ExtrinsicBaseWeight` should cost 1/10 of a CENT
	let base_fee = WeightToFee::calc(&ExtrinsicBaseWeight::get());
	let base_fee_expected = CENTS / 10;
	assert!(base_fee.max(base_fee_expected) - base_fee.min(base_fee_expected) < MILLICENTS);
}

fn run_with_system_weight<F>(w: Weight, mut assertions: F)
where
	F: FnMut(),
{
	let mut t: sp_io::TestExternalities = frame_system::GenesisConfig::default()
		.build_storage::<Runtime>()
		.unwrap()
		.into();
	t.execute_with(|| {
		System::set_block_consumed_resources(w, 0);
		assertions()
	});
}

#[test]
fn multiplier_can_grow_from_zero() {
	let minimum_multiplier = MinimumMultiplier::get();
	let target = TargetBlockFullness::get() * BlockWeights::get().get(DispatchClass::Normal).max_total.unwrap();
	// if the min is too small, then this will not change, and we are doomed forever.
	// the weight is 1/100th bigger than target.
	run_with_system_weight(target * 101 / 100, || {
		let next =
			TargetedFeeAdjustment::<Runtime, TargetBlockFullness, AdjustmentVariable, MinimumMultiplier>::convert(
				minimum_multiplier,
			);
		assert!(next > minimum_multiplier, "{:?} !>= {:?}", next, minimum_multiplier);
	})
}

#[test]
#[ignore]
fn multiplier_growth_simulator() {
	// calculate the value of the fee multiplier after one hour of operation with fully loaded blocks
	let mut multiplier = Multiplier::saturating_from_integer(1);
	let block_weight = BlockWeights::get().get(DispatchClass::Normal).max_total.unwrap();
	for _block_num in 1..=24 * HOURS {
		run_with_system_weight(block_weight, || {
			let next =
				TargetedFeeAdjustment::<Runtime, TargetBlockFullness, AdjustmentVariable, MinimumMultiplier>::convert(
					multiplier,
				);
			// ensure that it is growing as well.
			assert!(next > multiplier, "{:?} !>= {:?}", next, multiplier);
			multiplier = next;
		});
	}
	println!("multiplier = {:?}", multiplier);
}
