//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=120
// Creusot's `knights_tour` (`tests/should_succeed/vector/06_knights_tour.rs`, 3620de437), with
// Creusot's code and Thrust's annotations. Changes for Thrust: `Board::new` builds its rows in a
// `for` loop where Creusot's calls `map_inv(..).collect()` (creusot-std's `map_inv`); `knights_tour`
// has no `dumb_nonlinear_arith`, as Thrust (with `debug-assertions=off`) does not check overflow;
// `Point`'s fields and `Board`'s are read as the models they have.
use thrust_models::model::{int_lit, Int, Seq, UInt};
use thrust_models::{exists, forall, FnParam, Ghost, Model};

#[derive(Copy, Clone, PartialEq)]
struct Point {
    pub x: isize,
    pub y: isize,
}

impl Model for Point {
    type Ty = Point;
}

#[thrust_macros::context]
impl Point {
    #[thrust_macros::requires(-10000 <= self.x && self.x <= 10000)]
    #[thrust_macros::requires(-10000 <= self.y && self.y <= 10000)]
    #[thrust_macros::requires(-10000 <= p.0 && p.0 <= 10000)]
    #[thrust_macros::requires(-10000 <= p.1 && p.1 <= 10000)]
    #[thrust_macros::ensures(result.x == self.x + p.0)]
    #[thrust_macros::ensures(result.y == self.y + p.1)]
    fn mov(&self, p: &(isize, isize)) -> Self {
        Self { x: (self.x + p.0), y: (self.y + p.1) }
    }
}

#[derive(PartialEq)]
pub struct Board {
    pub size: usize,
    pub field: Vec<Vec<usize>>,
}

impl Model for Board {
    type Ty = Board;
}

#[thrust_macros::predicate]
fn wf(b: &Board) -> bool {
    b.size <= 1000
        && b.field.len() == b.size
        // `0 <= i` is needed: Thrust does not assume a `usize` bound by `forall` non-negative.
        && forall(|i: usize| !(0 <= i && i < b.size) || b.field[i].len() == b.size)
}

#[thrust_macros::predicate]
fn in_bounds(b: &Board, p: Point) -> bool {
    0 <= p.x && int_lit::<Int>(0) + p.x < b.size && 0 <= p.y && int_lit::<Int>(0) + p.y < b.size
}

#[thrust_macros::context]
impl Board {
    #[thrust_macros::requires(size <= 1000)]
    #[thrust_macros::ensures(result.size == size)]
    #[thrust_macros::ensures(wf(&result))]
    fn new(size: usize) -> Self {
        let mut rows = Vec::new();
        for _ in 0..size {
            thrust_macros::invariant!(|iter: core::ops::Range<usize>, iter_old: Ghost<core::ops::Range<usize>>, produced: Ghost<Seq<UInt>>, rows: Vec<Vec<usize>>, size: usize|
                iter_old.start == 0 && iter_old.end == size
                    && size <= 1000 && rows.len() == produced.len()
                    && forall(|i: Int| !(0 <= i && i < rows.len()) || rows[i].len() == size));
            rows.push(vec![0; size]);
        }
        Self { size, field: rows }
    }

    #[thrust_macros::requires(wf(self))]
    #[thrust_macros::ensures(result ==> in_bounds(self, p))]
    fn available(&self, p: Point) -> bool {
        0 <= p.x
            && (p.x as usize) < self.size
            && 0 <= p.y
            && (p.y as usize) < self.size
            && self.field[p.x as usize][p.y as usize] == 0
    }

    // calculate the number of possible moves
    #[thrust_macros::requires(wf(self))]
    #[thrust_macros::requires(in_bounds(self, p))]
    fn count_degree(&self, p: Point) -> usize {
        let mut count = 0;

        for m in moves() {
            thrust_macros::invariant!(|iter: std::vec::IntoIter<(isize, isize)>, iter_old: Ghost<std::vec::IntoIter<(isize, isize)>>, produced: Ghost<Seq<(Int, Int)>>, count: usize, self: FnParam<&Self>, p: Point|
                iter_old.1 == 0
                    && forall(|k: UInt| !(k < iter_old.0.len()) || (-2 <= iter_old.0[k].0 && iter_old.0[k].0 <= 2 && -2 <= iter_old.0[k].1 && iter_old.0[k].1 <= 2))
                    && wf(self.at_entry()) && in_bounds(self.at_entry(), p)
                    && count <= produced.len());
            let next = p.mov(&m);
            if self.available(next) {
                count += 1;
            }
        }
        count
    }

    #[thrust_macros::requires(wf(&*self))]
    #[thrust_macros::requires(in_bounds(&*self, p))]
    #[thrust_macros::ensures(wf(&!self))]
    #[thrust_macros::ensures((!self).size == (*self).size)]
    fn set(&mut self, p: Point, v: usize) {
        self.field[p.x as usize][p.y as usize] = v
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() == 8)]
#[thrust_macros::ensures(forall(|i: UInt| !(i < 8) || (-2 <= result[i].0 && result[i].0 <= 2 && -2 <= result[i].1 && result[i].1 <= 2)))]
fn moves() -> Vec<(isize, isize)> {
    let mut v = Vec::new();
    v.push((2, 1));
    v.push((1, 2));
    v.push((-1, 2));
    v.push((-2, 1));
    v.push((-2, -1));
    v.push((-1, -2));
    v.push((1, -2));
    v.push((2, -1));
    v
}

#[thrust_macros::context]
#[thrust_macros::ensures(forall(|r| result == Some(r) ==> exists(|i: Int| 0 <= i && i < v.len() && v[i] == *r)))]
fn min(v: &Vec<(usize, Point)>) -> Option<&(usize, Point)> {
    let mut min = None;
    for x in v {
        thrust_macros::invariant!(|iter: core::slice::Iter<'_, (usize, Point)>, iter_old: Ghost<core::slice::Iter<'_, (usize, Point)>>, produced: Ghost<Seq<&(UInt, Point)>>, min: Option<&(usize, Point)>, v: &Vec<(usize, Point)>|
            iter_old.0 == *v && iter_old.1 == 0
                && forall(|r| min == Some(r) ==> exists(|i: Int| 0 <= i && i < v.len() && v[i] == *r)));
        match min {
            None => min = Some(x),
            Some(m) => {
                if x.0 < m.0 {
                    min = Some(x)
                }
            }
        };
    }
    min
}

#[thrust_macros::context]
#[thrust_macros::requires(0 < size && size <= 1000)]
#[thrust_macros::requires(x < size)]
#[thrust_macros::requires(y < size)]
pub fn knights_tour(size: usize, x: usize, y: usize) -> Option<Board> {
    let mut board = Board::new(size);
    let mut p = Point { x: x as isize, y: y as isize };
    board.set(p, 1);

    for step in 2..(size * size) {
        thrust_macros::invariant!(|iter: core::ops::Range<usize>, board: Board, p: Point, size: usize|
            board.size == size && wf(&board) && in_bounds(&board, p));
        // choose next square by Warnsdorf's rule
        let mut candidates: Vec<(usize, Point)> = Vec::new();
        for m in moves() {
            thrust_macros::invariant!(|iter: std::vec::IntoIter<(isize, isize)>, iter_old: Ghost<std::vec::IntoIter<(isize, isize)>>, candidates: Vec<(usize, Point)>, board: Board, p: Point, size: usize|
                iter_old.1 == 0
                    && forall(|k: UInt| !(k < iter_old.0.len()) || (-2 <= iter_old.0[k].0 && iter_old.0[k].0 <= 2 && -2 <= iter_old.0[k].1 && iter_old.0[k].1 <= 2))
                    && board.size == size && wf(&board) && in_bounds(&board, p)
                    && forall(|i: Int| !(0 <= i && i < candidates.len()) || in_bounds(&board, candidates[i].1)));
            let adj = p.mov(&m);
            if board.available(adj) {
                let degree = board.count_degree(adj);
                candidates.push((degree, adj));
            }
        }
        match min(&candidates) {
            Some(&(_, adj)) => p = adj,
            None => return None,
        };
        board.set(p, step);
    }
    Some(board)
}
