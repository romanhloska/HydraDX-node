// This file is part of HydraDX.

// Copyright (C) 2020-2021  Intergalactic, Limited (GIB).
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
pub use crate::mock::{
	AssetRegistry, Currency, Event as TestEvent, ExtBuilder, Origin, System, Test, ACA, ALICE, Swap, BOB, DOT, HDX,
};
use frame_support::assert_ok;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut ext = ExtBuilder::default().build();
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn retrieve_pool_asset(pair: AssetPair) -> AssetId {
	AssetRegistry::get_or_create_asset(pair.name()).unwrap()
}

#[test]
fn create_pool_should_work() {
	new_test_ext().execute_with(|| {
		//let _ = Balances::deposit_creating(&1, 100000000);
		assert_ok!(Swap::create_pool(Origin::signed(ALICE), (0, 1), Balance::from(1u128),));
		let asset_pair = AssetPair {
			asset_in: 0,
			asset_out: 1,
		};

		let pool_asset = retrieve_pool_asset(asset_pair);

		assert_eq!(
			Swap::pools((0, 1)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (0, 0)
			})
		);
	});
}

#[test]
fn add_liquidity_should_work() {
	new_test_ext().execute_with(|| {
		//let _ = Balances::deposit_creating(&1, 100000000);
		assert_ok!(Swap::create_pool(
			Origin::signed(ALICE),
			(ACA, DOT),
			Balance::from(1u128),
		));

		let asset_pair = AssetPair {
			asset_in: ACA,
			asset_out: DOT,
		};

		let pool_asset = retrieve_pool_asset(asset_pair);

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (0, 0)
			})
		);

		assert_ok!(Swap::add_liquidity(
			Origin::signed(ALICE),
			(ACA, DOT),
			(Balance::from(1u128), Balance::from(100_000u128)),
			Balance::from(1u128)
		));

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (1, 100_000)
			})
		);

		assert_eq!(Currency::free_balance(pool_asset, &ALICE), 19822);
	});
}

#[test]
fn trades_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(Swap::create_pool(
			Origin::signed(ALICE),
			(ACA, DOT),
			Balance::from(1u128),
		));
		let asset_pair = AssetPair {
			asset_in: ACA,
			asset_out: DOT,
		};

		let pool_asset = retrieve_pool_asset(asset_pair);

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (0, 0)
			})
		);

		assert_ok!(Swap::add_liquidity(
			Origin::signed(ALICE),
			(ACA, DOT),
			(Balance::from(50_000u128), Balance::from(100_000u128)),
			Balance::from(1u128)
		));

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (50_000, 100_000)
			})
		);

		assert_ok!(Swap::sell(Origin::signed(BOB), DOT, ACA, 10_000, Balance::from(1u128)));

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (60_000, 87_971)
			})
		);
		assert_eq!(Currency::free_balance(DOT, &BOB), 999999999990000);
		assert_eq!(Currency::free_balance(ACA, &BOB), 1000000000012029);

		assert_ok!(Swap::buy(
			Origin::signed(BOB),
			DOT,
			ACA,
			10_000,
			Balance::from(15_000u128)
		));

		assert_eq!(
			Swap::pools((DOT, ACA)),
			Some(PoolInfo {
				pool_asset,
				amplification: 1,
				balances: (50_000, 100_613)
			})
		);
		assert_eq!(Currency::free_balance(DOT, &BOB), 1000000000000000);
		assert_eq!(Currency::free_balance(ACA, &BOB), 999999999999387);
	});
}
