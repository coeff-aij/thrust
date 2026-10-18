// The functions of a Rust file and their paths for THRUST_VERIFY_ONLY.

import * as assert from "assert";
import * as fs from "fs";
import * as path from "path";
import { test } from "node:test";
import { functionsIn, modulePathOf, selectionPath } from "../src/items";

const fixtures = path.join(__dirname, "..", "..", "test", "fixtures");

function paths(text: string): string[] {
  return functionsIn(text).map((f) => f.path.join("::"));
}

test("functions: free, of an inherent impl and of a trait impl, named as the selection names them", () => {
  const text = fs.readFileSync(path.join(fixtures, "cargo", "workspace", "arith", "src", "lib.rs"), "utf8");
  const found = functionsIn(text);
  assert.deepStrictEqual(
    found.map((f) => [f.path.join("::"), f.line, f.endLine]),
    [
      ["inc", 3, 6],
      ["Pair::twice", 11, 13],
      ["Pair::scale", 21, 23],
      ["sextuple", 26, 30],
    ],
  );
});

test("functions: the line of the first attribute, nested modules, trait default methods", () => {
  const text = [
    "/// Doc.",
    "#[thrust_macros::requires(x > 0)]",
    "#[thrust_macros::ensures(result >= x)]",
    "pub(crate) const unsafe fn f(x: i64) -> i64 { x }",
    "mod m {",
    "    pub mod n {",
    "        pub async fn g() {}",
    "    }",
    "    fn h() { let s = \"} fn no() {\"; let c = '}'; }",
    "}",
    "trait T {",
    "    fn required(&self);",
    "    fn provided(&self) -> u8 { 0 }",
    "}",
  ].join("\n");
  assert.deepStrictEqual(
    functionsIn(text).map((f) => [f.path.join("::"), f.line, f.endLine]),
    [
      ["f", 2, 4],
      ["m::n::g", 7, 7],
      ["m::h", 9, 9],
      ["T::provided", 13, 13],
    ],
  );
});

test("functions: impls of generic, qualified, reference, primitive and parameter types", () => {
  const text = [
    "impl<'a, T: Clone + Into<u8>, const N: usize> crate::a::Wrap<'a, T, N> where T: Copy { fn w() {} }",
    "impl<T> From<T> for Vec2<T> { fn from(t: T) -> Self { todo!() } }",
    "impl Tr for &Foo { fn r() {} }",
    "impl Tr for i64 { fn p() {} }",
    "impl<T> Tr for T { fn q() {} }",
    "impl dyn Tr { fn d() {} }",
    "unsafe impl Send for S { fn s() {} }",
  ].join("\n");
  assert.deepStrictEqual(paths(text), ["Wrap::w", "Vec2::from", "{impl}::r", "{impl}::p", "{impl}::q", "{impl}::d", "S::s"]);
});

test("functions: comments, raw strings, lifetimes and chars do not open or close a block", () => {
  const text = [
    "// fn commented() {",
    "/* nested /* fn c() { */ still } */",
    "fn a<'a>(x: &'a str) -> char { let _ = r#\"}\"#; let _ = b'{'; let _ = '\\''; 'x' }",
    "struct S { f: u8 }",
    "use std::{fmt, io};",
    "macro_rules! m { () => { fn generated() {} } }",
    "fn b() { fn inner() {} let _ = || { 1 }; }",
    "extern \"C\" { fn external(); }",
    "fn r#match() {}",
  ].join("\n");
  assert.deepStrictEqual(paths(text), ["a", "b", "match"]);
});

test("module paths: the crate root, a file next to it, a mod.rs, a file outside", () => {
  const root = path.join("/w", "src", "lib.rs");
  assert.deepStrictEqual(modulePathOf(root, root), []);
  assert.deepStrictEqual(modulePathOf(path.join("/w", "src", "ops.rs"), root), ["ops"]);
  assert.deepStrictEqual(modulePathOf(path.join("/w", "src", "a", "mod.rs"), root), ["a"]);
  assert.deepStrictEqual(modulePathOf(path.join("/w", "src", "a", "b.rs"), root), ["a", "b"]);
  assert.strictEqual(modulePathOf(path.join("/w", "tests", "t.rs"), root), undefined);
});

test("selection path: the module's path, then the function's in the file", () => {
  const [fn] = functionsIn("impl Pair { fn twice() {} }");
  assert.strictEqual(selectionPath(["ops"], fn), "ops::Pair::twice");
  assert.strictEqual(selectionPath([], fn), "Pair::twice");
});
