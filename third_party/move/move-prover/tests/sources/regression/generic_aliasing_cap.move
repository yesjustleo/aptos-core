// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// Past either cap on type-aliasing cases, verification must fail with a diagnostic rather
// than silently skip the remaining cases.
//
// A generic function is verified once per way its accessed resources can alias. The number
// of cases grows with the Bell numbers of the set of resources that can coincide: seven such
// resources give 877 cases, above the cap on cases, and ten exceed the cap on resources,
// checked before any case is enumerated. Truncating silently would leave aliasing cases
// unverified -- the unsoundness the derivation exists to prevent -- so both are errors.

module 0x42::generic_aliasing_cap {

    struct R<phantom T> has key {
        value: bool,
    }

    public fun seven<T1, T2, T3, T4, T5, T6, T7>(a: address): bool {
        R<T1>[a].value && R<T2>[a].value && R<T3>[a].value && R<T4>[a].value
            && R<T5>[a].value && R<T6>[a].value && R<T7>[a].value
    }
    spec seven {
        pragma aborts_if_is_partial;
        ensures result == true;
    }

    public fun ten<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(a: address): bool {
        R<T1>[a].value && R<T2>[a].value && R<T3>[a].value && R<T4>[a].value
            && R<T5>[a].value && R<T6>[a].value && R<T7>[a].value && R<T8>[a].value
            && R<T9>[a].value && R<T10>[a].value
    }
    spec ten {
        pragma aborts_if_is_partial;
        ensures result == true;
    }
}
