//! A lightweight, self-contained s-expression parser and data format.

// Needed for `is_char_boundary` and `char_range_at`. I'd love to remove this
// so that this library works on stable, but it involved a LOT of copy-paste
// from the standard library.
#![feature(str_char)]

#![deny(missing_docs)]
#![deny(unsafe_code)]

use std::str::{self, FromStr};

/// A single data element in an s-expression. Floats are excluded to ensure
/// atoms may be used as keys in ordered and hashed data structures.
///
/// All strings must be valid utf-8.
#[derive(Eq, Ord, PartialEq, Clone, PartialOrd, Debug, Hash)]
#[allow(missing_docs)]
pub enum Atom {
  S(String),
  I(i64),
}

/// An s-expression is either an atom or a list of s-expressions. This is
/// similar to the data format used by lisp.
#[derive(Eq, Ord, PartialEq, Clone, PartialOrd, Debug, Hash)]
#[allow(missing_docs)]
pub enum Sexp {
  Atom(Atom),
  List(Vec<Sexp>),
}

#[test]
fn sexp_size() {
  // I just want to see when this changes, in the diff.
  use std::mem;
  assert_eq!(mem::size_of::<Sexp>(), mem::size_of::<isize>()*5);
}

/// Helps clean up type signatures, but shouldn't be exposed to the outside
/// world.
type ERes<T> = Result<T, ()>;

/// A helpful utility to trace the execution of a parser while testing.  It will
/// be compiled out in release builds.
#[allow(unused_variables)]
fn dbg(msg: &str, pos: &usize) {
  //println!("{} @ {}", msg, pos)
}

fn atom_of_string(s: String) -> Atom {
  match FromStr::from_str(&s) {
    Ok(i)  => return Atom::I(i),
    Err(_) => {},
  };

  Atom::S(s)
}

// returns the char it found, and the new size if you wish to consume that char
fn peek(s: &str, pos: &usize) -> ERes<(char, usize)> {
  dbg("peek", pos);
  if *pos == s.len() { return Err(()) }
  if s.is_char_boundary(*pos) {
    let str::CharRange { ch, next } = s.char_range_at(*pos);
    Ok((ch, next))
  } else {
    Err(())
  }
}

fn expect(s: &str, pos: &mut usize, c: char) -> ERes<()> {
  dbg("expect", pos);
  let (ch, next) = try!(peek(s, pos));
  *pos = next;
  if ch == c { Ok(()) } else { Err(()) }
}

fn consume_until_newline(s: &str, pos: &mut usize) -> ERes<()> {
  loop {
    if *pos == s.len() { return Ok(()) }
    let (ch, next) = try!(peek(s, pos));
    *pos = next;
    if ch == '\n' { return Ok(()) }
  }
}

// zero or more spaces
fn zspace(s: &str, pos: &mut usize) -> ERes<()> {
  dbg("zspace", pos);
  loop {
    if *pos == s.len() { return Ok(()) }
    let (ch, next) = try!(peek(s, pos));

    if ch == ';'               { try!(consume_until_newline(s, pos)) }
    else if ch.is_whitespace() { *pos = next; }
    else                       { return Ok(()) }
  }
}

fn parse_quoted_atom(s: &str, pos: &mut usize) -> ERes<Atom> {
  dbg("parse_quoted_atom", pos);
  let mut cs: String = String::new();

  try!(expect(s, pos, '"'));

  loop {
    let (ch, next) = try!(peek(s, pos));
    if ch == '"' {
      *pos = next;
      break;
    } else if ch == '\\' {
      let (postslash, nextnext) = try!(peek(s, &next));
      if postslash == '"' || postslash == '\\' {
        cs.push(postslash);
      } else {
        cs.push(ch);
        cs.push(postslash);
      }
      *pos = nextnext;
    } else {
      cs.push(ch);
      *pos = next;
    }
  }

  Ok(atom_of_string(cs))
}

fn parse_unquoted_atom(s: &str, pos: &mut usize) -> ERes<Atom> {
  dbg("parse_unquoted_atom", pos);
  let mut cs: String = String::new();

  loop {
    if *pos == s.len() { break }
    let (c, next) = try!(peek(s, pos));

    if c == ';' { try!(consume_until_newline(s, pos)); break }
    if c.is_whitespace() || c == ')' { break }
    cs.push(c);
    *pos = next;
  }

  Ok(atom_of_string(cs))
}

fn parse_atom(s: &str, pos: &mut usize) -> ERes<Atom> {
  dbg("parse_atom", pos);
  let (ch, _) = try!(peek(s, pos));

  if ch == '"' { parse_quoted_atom  (s, pos) }
  else         { parse_unquoted_atom(s, pos) }
}

fn parse_list(s: &str, pos: &mut usize) -> ERes<Vec<Sexp>> {
  dbg("parse_list", pos);
  try!(zspace(s, pos));
  try!(expect(s, pos, '('));

  let mut sexps: Vec<Sexp> = Vec::new();

  loop {
    try!(zspace(s, pos));
    let (c, next) = try!(peek(s, pos));
    if c == ')' {
      *pos = next;
      break;
    }
    sexps.push(try!(parse_sexp(s, pos)));
  }

  try!(zspace(s, pos));

  Ok(sexps)
}

fn parse_sexp(s: &str, pos: &mut usize) -> ERes<Sexp> {
  dbg("parse_sexp", pos);
  try!(zspace(s, pos));
  let (c, _) = try!(peek(s, pos));
  let r =
    if c == '(' { Ok(Sexp::List(try!(parse_list(s, pos)))) }
    else        { Ok(Sexp::Atom(try!(parse_atom(s, pos)))) };
  try!(zspace(s, pos));
  r
}

/// Constructs an atomic s-expression from a string.
pub fn atom_s(s: &str) -> Sexp {
  Sexp::Atom(Atom::S(s.to_owned()))
}

/// Constructs an atomic s-expression from an int.
pub fn atom_i(i: i64) -> Sexp {
  Sexp::Atom(Atom::I(i))
}

/// Constructs a list s-expression given a slice of s-expressions.
pub fn list(xs: &[Sexp]) -> Sexp {
  Sexp::List(xs.to_owned())
}

/// Reads an s-expression out of a `&str`. Returns `Err(())` on parse error.
pub fn parse(s: &str) -> Result<Sexp, ()> {
  let mut pos = 0;
  let ret = try!(parse_sexp(s, &mut pos));
  if pos == s.len() { Ok(ret) } else { Err(()) }
}

#[test]
fn test_hello_world() {
  assert_eq!(
    parse("(hello -42\n\t  \"world\") ; comment"),
    Ok(list(&[ atom_s("hello"), atom_i(-42), atom_s("world") ])));
}
