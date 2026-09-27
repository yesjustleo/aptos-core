// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// A generic function must be verified in every way its accessed resources can alias.
//
// A generic function is verified at the open instantiation, where distinct type parameters
// are treated as distinct types, plus one extra instantiation per aliasing case. Those cases
// were derived only for pairs of accessed resources: with `R<T>`, `R<U>` and `R<V>`, the
// cases `T = U`, `T = V` and `U = V` were verified but `T = U = V` never was, so a
// postcondition false only when all three alias was proved. The cases are now derived from
// every partition of the resources that can coincide, one instantiation per partition whose
// blocks can be unified.

module 0x42::generic_aliasing_all_partitions {

    struct R<phantom T> has key {
        value: bool,
    }

    /// Must fail: false only at `T = U = V`, where all three writes hit one resource.
    public fun three_way<T, U, V>(a: address): bool {
        R<T>[a].value = false;
        R<U>[a].value = false;
        R<V>[a].value = true;
        R<T>[a].value == false || R<U>[a].value == false
    }
    spec three_way {
        requires exists<R<T>>(a) && exists<R<U>>(a) && exists<R<V>>(a);
        ensures result == true;
    }

    /// Must fail: false only at `A = B = C = D`, which takes more than one merge step to reach.
    public fun four_way<A, B, C, D>(a: address): bool {
        R<A>[a].value = false;
        R<B>[a].value = false;
        R<C>[a].value = false;
        R<D>[a].value = true;
        R<A>[a].value == false || R<B>[a].value == false || R<C>[a].value == false
    }
    spec four_way {
        requires exists<R<A>>(a) && exists<R<B>>(a) && exists<R<C>>(a) && exists<R<D>>(a);
        ensures result == true;
    }

    /// Must fail: the pairwise case, which was already derived.
    public fun pair<T, U>(a: address): bool {
        R<T>[a].value = false;
        R<U>[a].value = true;
        R<T>[a].value == false
    }
    spec pair {
        requires exists<R<T>>(a) && exists<R<U>>(a);
        ensures result == true;
    }

    /// Must verify: true in every aliasing case, including `T = U = V`.
    public fun true_in_every_case<T, U, V>(a: address): bool {
        R<T>[a].value = true;
        R<U>[a].value = true;
        R<V>[a].value = true;
        R<T>[a].value && R<U>[a].value && R<V>[a].value
    }
    spec true_in_every_case {
        requires exists<R<T>>(a) && exists<R<U>>(a) && exists<R<V>>(a);
        ensures result == true;
    }

    struct S<phantom T> has key {
        value: bool,
    }

    /// Must fail: false only at `T = U = u64`, a three-way case reached through a concrete type.
    public fun through_concrete<T, U>(a: address): bool {
        R<T>[a].value = false;
        R<U>[a].value = false;
        R<u64>[a].value = true;
        R<T>[a].value == false || R<U>[a].value == false
    }
    spec through_concrete {
        requires exists<R<T>>(a) && exists<R<U>>(a) && exists<R<u64>>(a);
        ensures result == true;
    }

    /// Must fail: false only at `T = U = V`, which needs a merge in `R` composed with one in `S`.
    public fun across_structs<T, U, V>(a: address): bool {
        R<T>[a].value = false;
        S<T>[a].value = false;
        R<U>[a].value = true;
        S<V>[a].value = true;
        R<T>[a].value == false || S<T>[a].value == false
    }
    spec across_structs {
        requires exists<R<T>>(a) && exists<S<T>>(a) && exists<R<U>>(a) && exists<S<V>>(a);
        ensures result == true;
    }

    /// Must fail: false only when `U = vector<T>` and `T = V`, merging through nested types.
    public fun through_nesting<T, U, V>(a: address): bool {
        R<vector<T>>[a].value = false;
        R<U>[a].value = false;
        R<vector<V>>[a].value = true;
        R<vector<T>>[a].value == false || R<U>[a].value == false
    }
    spec through_nesting {
        requires exists<R<vector<T>>>(a) && exists<R<U>>(a) && exists<R<vector<V>>>(a);
        ensures result == true;
    }

    /// Must verify, and must not hit the cap: `R<T>` and `R<vector<T>>` can never alias, but
    /// the unifier offers `T := vector<T>`, which repeated would only ever deepen both types.
    public fun never_alias<T>(a: address): bool {
        R<T>[a].value = true;
        R<vector<T>>[a].value = true;
        R<T>[a].value
    }
    spec never_alias {
        requires exists<R<T>>(a) && exists<R<vector<T>>>(a);
        ensures result == true;
    }

    struct X<phantom A, phantom B> has key {
        value: bool,
    }

    struct Y<phantom A, phantom B> has key {
        value: bool,
    }

    /// Must fail: false only when both pairs alias at once, `T3 = T2 = u64` and
    /// `T0 = T1 = vector<u64>`. Reaching it takes a merge that aliases nothing by itself.
    public fun two_pairs<T0, T1, T2, T3>(a: address): bool {
        Y<T3, T1>[a].value = false;
        X<vector<T3>, vector<T2>>[a].value = false;
        Y<u64, T0>[a].value = true;
        X<T0, vector<T3>>[a].value = true;
        Y<T3, T1>[a].value == false || X<vector<T3>, vector<T2>>[a].value == false
    }
    spec two_pairs {
        requires exists<Y<T3, T1>>(a) && exists<X<vector<T3>, vector<T2>>>(a)
            && exists<Y<u64, T0>>(a) && exists<X<T0, vector<T3>>>(a);
        ensures result == true;
    }

    /// Must fail: false only at `T0 = T1 = T2 = u64`, where the memories share type parameters,
    /// so merging one pair changes what the others can unify with.
    public fun three_shared<T0, T1, T2>(a: address): bool {
        X<T2, T1>[a].value = false;
        X<T1, T0>[a].value = false;
        X<u64, T0>[a].value = true;
        X<T2, T1>[a].value == false || X<T1, T0>[a].value == false
    }
    spec three_shared {
        requires exists<X<T2, T1>>(a) && exists<X<T1, T0>>(a) && exists<X<u64, T0>>(a);
        ensures result == true;
    }
}
