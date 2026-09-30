//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// rustc's caller (rustc_ty_utils::layout, `ty::Coroutine`) establishes the dimension,
// well-formedness and index conjuncts of `layout()`'s panic-safety precondition from a
// `CoroutineLayout` built as
// rustc_mir_transform's `compute_layout` builds it: one layout per saved local, `storage_conflicts`
// sized by the number of saved locals, each variant listing saved locals below that number.
// `layout` keeps only the arguments the conjuncts name; indices are `usize`, and `Idx::can_new` of
// rustc's index types is their bound 0xFFFF_FF00. `BitMatrix::new` is rustc's, with the words'
// count as `num_words` computes it.

use thrust_models::model::Int;

pub struct BitMatrix {
    num_rows: usize,
    num_columns: usize,
    words: Vec<u64>,
}

impl thrust_models::Model for BitMatrix {
    type Ty = Self;
}

#[thrust_macros::context]
impl BitMatrix {
    #[thrust_macros::predicate]
    fn wf(self) -> bool {
        thrust_models::exists(|rw: Int| {
            self.words.len() == self.num_rows * rw
                && 64 * rw >= self.num_columns
                && 64 * rw < self.num_columns + 64
        })
    }

    fn new(num_rows: usize, num_columns: usize) -> BitMatrix {
        let words_per_row = num_columns.div_ceil(64);
        BitMatrix { num_rows, num_columns, words: vec![0; num_rows * words_per_row] }
    }
}

#[thrust::trusted]
#[thrust_macros::requires((*variant_fields).len() > 0
    && (*storage_conflicts).num_rows <= (*local_layouts).len()
    && (*storage_conflicts).num_columns <= (*storage_conflicts).num_rows
    && BitMatrix::wf(*storage_conflicts)
    && thrust_models::forall(|v: Int| thrust_models::forall(|f: Int|
        (0 <= v && v < (*variant_fields).len() && 0 <= f && f < (*variant_fields)[v].len())
            ==> (*variant_fields)[v][f] < (*local_layouts).len()))
    && thrust_models::forall(|k: Int|
        (0 <= k && k < (*local_layouts).len()) ==> k <= 4294967040usize)
    && (*variant_fields).len() <= 4294967040usize
    && prefix_layouts.len() + 1 + (*local_layouts).len() <= 4294967040usize
    && thrust_models::forall(|v: Int|
        (0 <= v && v < (*variant_fields).len()) ==> (*variant_fields)[v].len() <= 4294967040usize)
    && prefix_layouts.len() + 1 + (*local_layouts).len() <= 4294967295usize)]
#[thrust_macros::ensures(true)]
fn layout(
    local_layouts: &Vec<u64>,
    prefix_layouts: Vec<u64>,
    variant_fields: &Vec<Vec<usize>>,
    storage_conflicts: &BitMatrix,
) {
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 2)]
fn saved_local_layouts() -> Vec<u64> {
    let mut layouts = Vec::new();
    layouts.push(8_u64);
    layouts.push(4);
    layouts
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 1 && result[0] == local)]
fn fields(local: usize) -> Vec<usize> {
    let mut fields = Vec::new();
    fields.push(local);
    fields
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 2 && result[0] == a && result[1] == b)]
fn fields2(a: usize, b: usize) -> Vec<usize> {
    let mut fields = Vec::new();
    fields.push(a);
    fields.push(b);
    fields
}

fn main() {
    let local_layouts = saved_local_layouts();
    let prefix_layouts = Vec::new();
    let storage_conflicts = BitMatrix::new(local_layouts.len() + 1, local_layouts.len() + 1);
    let mut variant_fields: Vec<Vec<usize>> = Vec::new();
    variant_fields.push(fields2(0, 1));
    variant_fields.push(fields(1));
    layout(&local_layouts, prefix_layouts, &variant_fields, &storage_conflicts);
}
