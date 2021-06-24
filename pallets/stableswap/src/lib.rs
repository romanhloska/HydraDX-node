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

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::unused_unit)]
#![allow(clippy::upper_case_acronyms)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

use frame_support::codec::{Decode, Encode};
use frame_support::ensure;
use frame_support::sp_runtime::{
	traits::{Hash, Zero},
	DispatchError,
};
use frame_system::ensure_signed;
use primitives::{asset::AssetPair, AssetId, Balance};
use sp_std::{marker::PhantomData, vec::Vec};

use frame_support::sp_runtime::app_crypto::sp_core::crypto::UncheckedFrom;
use orml_traits::{MultiCurrency, MultiCurrencyExtended};
use primitives::Amount;

use sp_runtime::traits::CheckedMul;

#[derive(Encode, Decode, Clone, Default, PartialEq, Eq, Debug)]
pub struct PoolInfo<AssetId, Number, Balance> {
	pool_asset: AssetId,
	amplification: Number,
	balances: (Balance, Balance),
}

impl PoolInfo<AssetId, Balance, Balance> {
	fn balance_for(&self, pair: AssetPair, asset: AssetId) -> Balance {
		let pair = pair.ordered_pair();

		if pair.0 == asset {
			return self.balances.0;
		}

		return self.balances.1;
	}
}

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::OriginFor;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {}

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_asset_registry::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type AssetPairAccountId: AssetPairAccountIdFor<AssetId, Self::AccountId>;

		/// The origin which can create a new pool
		type CreatePoolOrigin: EnsureOrigin<Self::Origin>;

		type Currency: MultiCurrencyExtended<Self::AccountId, CurrencyId = AssetId, Balance = Balance, Amount = Amount>;
	}

	#[pallet::error]
	pub enum Error<T> {
		PoolNotFound,
		Overflow,
		InvalidAssetAmount,
		MintAmountNotReached,
		InsufficientFunds,
		RequiredAmountNotReached,

		/// Pool cannot be created with same assets.
		SameAssetPool,

		/// Pool already exists.
		PoolAlreadyCreated,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// New liquidity was provided to the pool. [who, asset_a, asset_b, amount_a, amount_b]
		LiquidityAdded(T::AccountId, AssetId, AssetId, Balance, Balance),

		/// Liquidity was removed from the pool. [who, asset_a, asset_b, shares]
		LiquidityRemoved(T::AccountId, AssetId, AssetId, Balance),

		/// Pool was created
		PoolCreated(AssetId, AssetId),

		/// Pool was destroyed. [who, asset a, asset b]
		PoolDestroyed(T::AccountId, AssetId, AssetId),

		/// Asset sale executed. [who, asset in, asset out, amount, sale price]
		SellExecuted(T::AccountId, AssetId, AssetId, Balance, Balance),

		/// Asset purchase executed. [who, asset out, asset in, amount, buy price]
		BuyExecuted(T::AccountId, AssetId, AssetId, Balance, Balance),
	}

	/// Existing pools
	#[pallet::storage]
	#[pallet::getter(fn pools)]
	pub type Pools<T: Config> =
		StorageMap<_, Blake2_128Concat, (AssetId, AssetId), PoolInfo<AssetId, Balance, Balance>, OptionQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn create_pool(
			origin: OriginFor<T>,
			assets: (AssetId, AssetId),
			amplification: Balance,
		) -> DispatchResultWithPostInfo {
			T::CreatePoolOrigin::ensure_origin(origin)?;

			// Same assets
			ensure!(assets.0 != assets.1, Error::<T>::SameAssetPool);

			let asset_pair = AssetPair {
				asset_in: assets.0,
				asset_out: assets.1,
			};

			Pools::<T>::try_mutate_exists(asset_pair.ordered_pair(), |maybe_pool| -> DispatchResultWithPostInfo {
				ensure!(maybe_pool.is_none(), Error::<T>::PoolAlreadyCreated);

				let asset_name = asset_pair.name();

				let pool_asset = <pallet_asset_registry::Pallet<T>>::get_or_create_asset(asset_name)?.into();

				*maybe_pool = Some(PoolInfo {
					pool_asset: pool_asset,
					amplification: amplification,
					balances: (Balance::zero(), Balance::zero()),
				});

				Self::deposit_event(Event::PoolCreated(assets.0, assets.1));

				Ok(().into())
			})
		}

		#[pallet::weight(0)]
		pub fn add_liquidity(
			origin: OriginFor<T>,
			assets: (AssetId, AssetId),
			amounts: (Balance, Balance),
			min_mint_amount: Balance,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let asset_pair = AssetPair {
				asset_in: assets.0,
				asset_out: assets.1,
			};

			Pools::<T>::try_mutate(asset_pair.ordered_pair(), |pool| -> Result<_, DispatchError> {
				let pool = pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let ann = Self::get_ann(pool.amplification).ok_or(Error::<T>::Overflow)?;

				let d0 = Self::get_d(&[pool.balances.0, pool.balances.1], ann).ok_or(Error::<T>::Overflow)?;

				let supply = T::Currency::total_issuance(pool.pool_asset);

				let new_balance_a = pool.balances.0.checked_add(amounts.0).ok_or(Error::<T>::Overflow)?;
				let new_balance_b = pool.balances.1.checked_add(amounts.1).ok_or(Error::<T>::Overflow)?;

				let d1 = Self::get_d(&[new_balance_a, new_balance_b], ann).ok_or(Error::<T>::Overflow)?;
				ensure!(d1 > d0, Error::<T>::InvalidAssetAmount);

				pool.balances = (new_balance_a, new_balance_b);
				let mint_amount = d1;

				ensure!(mint_amount >= min_mint_amount, Error::<T>::MintAmountNotReached);

				let _new_token_supply = supply.checked_add(mint_amount).ok_or(Error::<T>::Overflow)?;

				ensure!(
					T::Currency::free_balance(assets.0, &who) >= amounts.0,
					Error::<T>::InsufficientFunds
				);
				ensure!(
					T::Currency::free_balance(assets.1, &who) >= amounts.1,
					Error::<T>::InsufficientFunds
				);

				let pool_account = Self::get_pair_id(asset_pair);

				T::Currency::deposit(pool.pool_asset, &who, mint_amount)?;

				T::Currency::transfer(assets.0, &who, &pool_account, amounts.0)?;

				T::Currency::transfer(assets.1, &who, &pool_account, amounts.1)?;

				Ok(())
			})?;
			Ok(().into())
		}

		#[pallet::weight(0)]
		pub fn sell(
			origin: OriginFor<T>,
			asset_sell: AssetId,
			asset_buy: AssetId,
			amount: Balance,
			min_bought: Balance,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			//let prec = Balance::from(1_000_u128);

			let asset_pair = AssetPair {
				asset_in: asset_sell,
				asset_out: asset_buy,
			};

			Pools::<T>::try_mutate(asset_pair.ordered_pair(), |pool| -> Result<_, DispatchError> {
				let pool = pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let balance_in = pool.balance_for(asset_pair, asset_sell);
				let balance_out = pool.balance_for(asset_pair, asset_buy);

				let new_in_balance = balance_in.checked_add(amount).ok_or(Error::<T>::Overflow)?;

				let ann = Self::get_ann(pool.amplification).ok_or(Error::<T>::Overflow)?;
				//let y = Self::get_y(0, 1, new_in_balance, &[balance_in, balance_out],ann).ok_or(Error::<T>::Overflow)?;
				let y = Self::get_y(
					0,
					1,
					Balance::from(new_in_balance),
					&[Balance::from(balance_in), Balance::from(balance_out)],
					Balance::from(ann),
				)
				.ok_or(Error::<T>::Overflow)?;

				let n_dy = balance_out.checked_sub(y).ok_or(Error::<T>::Overflow)?;

				ensure!(n_dy >= min_bought, Error::<T>::RequiredAmountNotReached);

				let new_balance_in = balance_in.checked_add(amount).ok_or(Error::<T>::Overflow)?;
				let new_balance_out = balance_out.checked_sub(n_dy).ok_or(Error::<T>::Overflow)?;

				pool.balances = if asset_sell <= asset_buy {
					(new_balance_in, new_balance_out)
				} else {
					(new_balance_out, new_balance_in)
				};

				let pool_account = Self::get_pair_id(asset_pair);

				ensure!(
					T::Currency::free_balance(asset_sell, &who) >= amount,
					Error::<T>::InsufficientFunds
				);
				ensure!(
					T::Currency::free_balance(asset_buy, &pool_account) >= n_dy,
					Error::<T>::InsufficientFunds
				);

				T::Currency::transfer(asset_sell, &who, &pool_account, amount)?;
				T::Currency::transfer(asset_buy, &pool_account, &who, n_dy)?;

				Ok(())
			})?;

			Ok(().into())
		}
		#[pallet::weight(0)]
		pub fn buy(
			origin: OriginFor<T>,
			asset_buy: AssetId,
			asset_sell: AssetId,
			amount: Balance,
			max_sold: Balance,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			//let prec = Balance::from(1_000_u128);

			let asset_pair = AssetPair {
				asset_in: asset_sell,
				asset_out: asset_buy,
			};

			Pools::<T>::try_mutate(asset_pair.ordered_pair(), |pool| -> Result<_, DispatchError> {
				let pool = pool.as_mut().ok_or(Error::<T>::PoolNotFound)?;

				let balance_in = pool.balance_for(asset_pair, asset_sell);
				let balance_out = pool.balance_for(asset_pair, asset_buy);

				let new_out_balance = balance_out.checked_sub(amount).ok_or(Error::<T>::Overflow)?;

				let ann = Self::get_ann(pool.amplification).ok_or(Error::<T>::Overflow)?;

				let y =
					Self::get_y(0, 1, new_out_balance, &[balance_out, balance_in], ann).ok_or(Error::<T>::Overflow)?;

				let n_dy = y.checked_sub(balance_in).ok_or(Error::<T>::Overflow)?;

				ensure!(n_dy <= max_sold, Error::<T>::RequiredAmountNotReached);

				let new_balance_in = balance_in.checked_add(n_dy).ok_or(Error::<T>::Overflow)?;
				let new_balance_out = balance_out.checked_sub(amount).ok_or(Error::<T>::Overflow)?;

				pool.balances = if asset_sell <= asset_buy {
					(new_balance_in, new_balance_out)
				} else {
					(new_balance_out, new_balance_in)
				};

				let pool_account = Self::get_pair_id(asset_pair);

				ensure!(
					T::Currency::free_balance(asset_sell, &who) >= n_dy,
					Error::<T>::InsufficientFunds
				);
				ensure!(
					T::Currency::free_balance(asset_buy, &pool_account) >= amount,
					Error::<T>::InsufficientFunds
				);

				T::Currency::transfer(asset_sell, &who, &pool_account, n_dy)?;
				T::Currency::transfer(asset_buy, &pool_account, &who, amount)?;

				Ok(())
			})?;

			Ok(().into())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Find `ann = amp * n^n` where `amp` - amplification coefficient,
	/// `n` - number of coins.
	pub(crate) fn get_ann(amp: Balance) -> Option<Balance> {
		let n_coins: Balance = Balance::from(2u128);
		let mut ann = amp;
		for _ in 0..2 {
			ann = ann.checked_mul(n_coins)?;
		}
		Some(ann)
	}

	pub(crate) fn get_d(xp: &[Balance], ann: Balance) -> Option<Balance> {
		let prec = Balance::from(10_000_u128);
		let zero = Balance::zero();
		let one = Balance::from(1_u128);

		let n_coins = Balance::from(2_u128);

		let mut s = zero;

		for x in xp.iter() {
			s = s.checked_add(*x)?;
		}
		if s == zero {
			return Some(zero);
		}

		let mut d = s;

		for _ in 0..255 {
			let mut d_p = d;
			for x in xp.iter() {
				// d_p = d_p * d / (x * n_coins)
				d_p = d_p.checked_mul(d)?.checked_div(x.checked_mul(&n_coins)?)?;
			}
			let d_prev = d;
			// d = (ann * s + d_p * n_coins) * d / ((ann - 1) * d + (n_coins + 1) * d_p)
			d = ann
				.checked_mul(s)?
				.checked_add(d_p.checked_mul(n_coins)?)?
				.checked_mul(d)?
				.checked_div(
					ann.checked_sub(one)?
						.checked_mul(d)?
						.checked_add(n_coins.checked_add(one)?.checked_mul(d_p)?)?,
				)?;

			if d > d_prev {
				if d.checked_sub(d_prev)? <= prec {
					return Some(d);
				}
			} else {
				if d_prev.checked_sub(d)? <= prec {
					return Some(d);
				}
			}
		}
		None
	}

	pub(crate) fn get_y(i: usize, j: usize, x: Balance, xp: &[Balance], ann: Balance) -> Option<Balance> {
		let prec = Balance::from(10_000_u128);
		let zero = Balance::zero();
		let two = Balance::from(2_u128);

		let n = two;

		// Same coin
		if !(i != j) {
			return None;
		}
		// j above n
		if !(j < xp.len()) {
			return None;
		}
		if !(i < xp.len()) {
			return None;
		}

		let d = Self::get_d(xp, ann)?;

		let mut c = d;
		let mut s = zero;

		// Calculate s and c
		// p is implicitly calculated as part of c
		// note that loop makes n - 1 iterations
		for k in 0..xp.len() {
			let x_k;
			if k == i {
				x_k = x;
			} else if k != j {
				x_k = xp[k];
			} else {
				continue;
			}
			// s = s + x_k
			s = s.checked_add(x_k)?;
			// c = c * d / (x_k * n)
			c = c.checked_mul(d)?.checked_div(x_k.checked_mul(n)?)?;
		}
		// c = c * d / (ann * n)
		// At this step we have d^n in the numerator of c
		// and n^(n-1) in its denominator.
		// So we multiplying it by remaining d/n
		c = c.checked_mul(d)?.checked_div(ann.checked_mul(n)?)?;

		// b = s + d / ann
		// We subtract d later
		let b = s.checked_add(d.checked_div(ann)?)?;
		let mut y = d;

		for _ in 0..255 {
			let y_prev = y;
			// y = (y^2 + c) / (2 * y + b - d)
			// Subtract d to calculate b finally
			y = y
				.checked_mul(y)?
				.checked_add(c)?
				.checked_div(two.checked_mul(y)?.checked_add(b)?.checked_sub(d)?)?;

			// Equality with the specified precision
			if y > y_prev {
				if y.checked_sub(y_prev)? <= prec {
					return Some(y);
				}
			} else {
				if y_prev.checked_sub(y)? <= prec {
					return Some(y);
				}
			}
		}

		None
	}

	fn get_pair_id(assets: AssetPair) -> T::AccountId {
		T::AssetPairAccountId::from_assets(assets.asset_in, assets.asset_out)
	}
}

pub trait AssetPairAccountIdFor<AssetId: Sized, AccountId: Sized> {
	fn from_assets(asset_a: AssetId, asset_b: AssetId) -> AccountId;
}

pub struct AssetPairAccountId<T: Config>(PhantomData<T>);

impl<T: Config> AssetPairAccountIdFor<AssetId, T::AccountId> for Pallet<T>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	fn from_assets(asset_a: AssetId, asset_b: AssetId) -> T::AccountId {
		let mut buf = Vec::new();
		buf.extend_from_slice(b"hydradx");
		if asset_a < asset_b {
			buf.extend_from_slice(&asset_a.to_le_bytes());
			buf.extend_from_slice(&asset_b.to_le_bytes());
		} else {
			buf.extend_from_slice(&asset_b.to_le_bytes());
			buf.extend_from_slice(&asset_a.to_le_bytes());
		}
		T::AccountId::unchecked_from(T::Hashing::hash(&buf[..]))
	}
}
