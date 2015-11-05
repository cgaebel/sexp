#![feature(str_char)]

use std::str::{self, FromStr};

#[derive(Eq, Ord, PartialEq, Clone, PartialOrd, Debug)]
pub enum Atom {
  S(Box<str>),
  I(i64),
}

#[derive(Eq, Ord, PartialEq, Clone, PartialOrd, Debug)]
pub enum Sexp {
  Atom(Atom),
  List(Vec<Sexp>),
}

#[test]
fn sexp_size() {
  use std::mem;
  assert_eq!(mem::size_of::<Sexp>(), mem::size_of::<isize>()*4);
}

type ERes<T> = Result<T, ()>;

#[allow(unused_variables)]
fn dbg(msg: &str, pos: &usize) {
  //println!("{} @ {}", msg, pos)
}

fn atom_of_string(s: String) -> Atom {
  match FromStr::from_str(&s) {
    Ok(i)  => return Atom::I(i),
    Err(_) => {},
  }

  Atom::S(s.into_boxed_str())
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

#[allow(dead_code)]
pub fn atom_s(s: &str) -> Sexp {
  Sexp::Atom(Atom::S(s.to_owned().into_boxed_str()))
}

#[allow(dead_code)]
pub fn atom_i(i: i64) -> Sexp {
  Sexp::Atom(Atom::I(i))
}

#[allow(dead_code)]
pub fn list(xs: &[Sexp]) -> Sexp {
  Sexp::List(xs.to_owned())
}

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
