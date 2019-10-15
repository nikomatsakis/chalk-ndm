//! Tests targeting auto traits specifically

use super::*;

// FIXME(rust-lang/chalk#218) -- this should
#[test]
#[should_panic(expected = "cannot unify things with binders")]
fn dyn_trait_success() {
    test! {
        program {
            trait Foo { }
            trait Bar { }
        }

        goal {
            dyn Foo: Foo
        } yields {
            "Unique"
        }

        goal {
            dyn Foo: Bar
        } yields {
            "error"
        }
    }
}
