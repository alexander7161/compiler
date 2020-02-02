// A parser and interpreter for the While language
// 

import scala.language.implicitConversions    
import scala.language.reflectiveCalls

// regular expressions including records
abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class PLUS(r: Rexp) extends Rexp 
case class OPTIONAL(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class RANGE(charSet: Set[Char]) extends Rexp

// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

case class PlusVal(vs: List[Val]) extends Val
case class OptionalVal(v: Val) extends Val
case class NtimesVal(vs: List[Val]) extends Val
case class RangeVal(charSet: Set[Char]) extends Val
   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) => true
  case RANGE(_) => false
}

def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
  case NTIMES(r, i) => if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r) => der(c, r)
  case RANGE(cs) => if (cs(c)) ONE else ZERO
}


// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
  case PlusVal(vs) => vs.map(flatten).mkString
}


// extracts an environment from a value;
// used for tokenise a string
def env(v: Val) : Prog = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
  case PlusVal(vs) => vs.flatMap(env)
  case OptionalVal(v) => env(v)
  case NtimesVal(vs) => vs.flatMap((env))
  case RangeVal(_) => Nil
}

// The Injection Part of the lexer

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
  case PLUS(r) => PlusVal(Nil)
  case OPTIONAL(_) => Empty
  case NTIMES(r, n) => NtimesVal(Nil)
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (NTIMES(r, n), Sequ(v, NtimesVal(vs))) => NtimesVal(inj(r, c, v) :: vs)
  case (NTIMES(r,n) , Empty) => NtimesVal(List[Val](Chr(c)))
  case (PLUS(r), Sequ(v, Stars(vs))) => PlusVal(inj(r, c, v) :: vs)
  case (OPTIONAL(r), v) => OptionalVal(inj(r, c, v))
  case (RANGE(cs), Empty) => Chr(c)
}

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    {  throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


val AtoZ = ('a' to 'z').toSet
val AtoZCapital = ('A' to 'Z').toSet

val LETTERS = RANGE(AtoZ ++ AtoZCapital)
val SYM = RANGE(AtoZ ++ AtoZCapital + '_')
val DIGIT = RANGE(('0' to '9').toSet)
val NONZERODIGITS = RANGE(('1' to '9').toSet)
val ID = LETTERS ~ (SYM | DIGIT).% 
val NUM = (NONZERODIGITS ~ STAR(DIGIT)) | "0"
val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" | "for" | "upto"
val SEMI: Rexp = ";"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ":=" | "&&" | "||" |"<="
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = "("
val LPAREN: Rexp = ")"
val RPARENCURLY: Rexp = "{"
val LPARENCURLY: Rexp = "}"
val STRING: Rexp = "\"" ~ SYM.% ~ "\""


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN | LPARENCURLY | RPARENCURLY)) | 
                  ("w" $ WHITESPACE)).%

type Prog = List[(String, String)]

def removeWhitespace(tks: Prog) =
  tks.filter{ case (s1, s2) => s1 != "w" }

def whileLex(prog: String) = removeWhitespace(lexing_simp(WHILE_REGS, prog))

// Parser

// more convenience for the semantic actions later on
case class ~[+A, +B](_1: A, _2: B)


type IsSeq[A] = A => Seq[_]

abstract class Parser[I : IsSeq, T] {
  def parse(ts: I): Set[(T, I)]

  def parse_all(ts: I) : Set[T] =
    for ((head, tail) <- parse(ts); if (tail.isEmpty)) yield head
}

class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I : IsSeq, T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I : IsSeq, T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

case object NumParser extends Parser[Prog, Int] {
    def parse(tks: Prog) = tks match {
        case ("n", n) :: rest => Set((n.toInt, rest))
        case _ => Set()
    }
}

case class TokenParser(t: (String,String)) extends Parser[Prog, String] {
    def parse(tks: Prog) = tks match {
        case head :: rest if (head == t) => Set((head._2, rest))
        case _ => Set()
    }
}

case object IdParser extends Parser[Prog, String] {
    def parse(tks: Prog) = tks match {
        case ("i", s) :: rest => Set((s, rest))
        case _ => Set()
        
    }
}

case object StrTokenParser extends Parser[Prog, String] {
    def parse(tks: Prog) = tks match {
        case ("str", s) :: rest =>  Set((s, rest))
        case _ => Set()
    }
}

implicit def token2parser(t : (String, String)) = TokenParser(t)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

implicit def TokenOps(t: (String, String)) = new {
    def ==>[S] (f: => String => S) = new FunParser[Prog, String, S](t, f)
    def ~[S](q : => Parser[Prog, S]) = 
        new SeqParser[Prog, String, S](t, q)
    def ~ (r: (String, String)) = new SeqParser[Prog, String, String](t, r)
}


// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class For(a1: Stmt, a2: AExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class WriteID(a: String) extends Stmt
case class Read(s: String) extends Stmt


case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

lazy val AExp: Parser[Prog, AExp] = 
  (Te ~ ("o", "+") ~ AExp) ==> { case x ~ y ~ z => Aop("+", x, z): AExp } ||
  (Te ~ ("o", "-") ~ AExp) ==> { case x ~ y ~ z => Aop("-", x, z): AExp } || Te 
lazy val Te: Parser[Prog, AExp] = 
  (Fa ~ ("o", "*") ~ Te) ==> { case x ~ y ~ z => Aop("*", x, z): AExp } || 
  (Fa ~ ("o", "/") ~ Te) ==> { case x ~ y ~ z => Aop("/", x, z): AExp } || Fa  
lazy val Fa: Parser[Prog, AExp] = 
   (("p", "(") ~ AExp ~ ("p", ")")) ==> { case x ~ y ~ z => y } || 
   IdParser ==> Var || 
   NumParser ==> Num

// boolean expressions with some simple nesting
lazy val BExp: Parser[Prog, BExp] = 
   (AExp ~ ("o", "==") ~ AExp) ==> { case x ~ y ~ z => Bop("==", x, z): BExp } || 
   (AExp ~ ("o", "!=") ~ AExp) ==> { case x ~ y ~ z => Bop("!=", x, z): BExp } || 
   (AExp ~ ("o", "<") ~ AExp) ==> { case x ~ y ~ z => Bop("<", x, z): BExp } || 
   (AExp ~ ("o", ">") ~ AExp) ==> { case x ~ y ~ z => Bop(">", x, z): BExp } ||
   (AExp ~ ("o", "<=") ~ AExp) ==> { case x ~ y ~ z => Bop("<=", x, z): BExp } || 
   (("p", "(") ~ BExp ~ ("p", ")") ~ ("o", "&&") ~ BExp) ==> { case x ~ y ~ z ~ u ~ v => And(y, v): BExp } ||
   (("p", "(") ~ BExp ~ ("p", ")") ~ ("o", "||") ~ BExp) ==> { case x ~ y ~ z ~ u ~ v => Or(y, v): BExp } ||
   (("k", "true") ==> (_ => True: BExp )) || 
   (("k", "false") ==> (_ => False: BExp )) ||
   (("p", "(") ~ BExp ~ ("p", ")")) ==> { case x ~ y ~ z => y}

// statement / statements
lazy val Stmt: Parser[Prog, Stmt] =
  (("k", "skip") ==> (_ => Skip: Stmt)) ||
   (IdParser ~ ("o", ":=") ~ AExp) ==> { case x ~ y ~ z => Assign(x, z): Stmt } ||
   (("k", "if") ~ BExp ~ ("k", "then") ~ Block ~ ("k", "else") ~ Block) ==>
    { case x ~ y ~ z ~ u ~ v ~ w => If(y, u, w): Stmt } ||
   (("k", "for") ~ IdParser ~ ("o", ":=") ~ AExp ~ ("k", "upto") ~ AExp ~ ("k", "do") ~ Block) ==> 
   { case _ ~ y ~ _ ~ u ~ _ ~ w ~ _ ~ r => For(Assign(y, u), w, r) } ||
   (("k", "while") ~ BExp ~ ("k", "do") ~ Block) ==> { case x ~ y ~ z ~ w => While(y, w) } ||
    (("k", "write") ~ StrTokenParser ==> { case x ~ y => Write(y): Stmt} ) ||
    (("k", "write") ~ IdParser ==> { case x ~ y => WriteID(y): Stmt }) ||
    (("k", "read") ~ IdParser ==> { case x ~ y => Read(y): Stmt })
 
lazy val Stmts: Parser[Prog, Block] =
  (Stmt ~ ("s", ";") ~ Stmts) ==> { case x ~ y ~ z => x :: z : Block } ||
  (Stmt ==> ( s => List(s) : Block))

// blocks (enclosed in curly braces)
lazy val Block: Parser[Prog, Block] =
  (("p", "{") ~ Stmts ~ ("p", "}")) ==> { case x ~ y ~ z => y} || 
  (Stmts) ==> { case x => x : Block }

type Env = Map[String, Int]

// compiler headers needed for the JVM
// (contains methods for read and write)
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method

.method public static writeString(Ljava/lang/String;)V
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return 
.end method

.method public static read()I 
    .limit locals 10 
    .limit stack 10

    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream; 
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 10   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2

    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ;when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""

// Compiler functions


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// convenient string interpolations 
// for instructions and labels
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

// this allows you to write things like
// i"add" and l"Label"


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
}

// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

// boolean expression compilation
//  - the jump-label is for where to jump if the condition is not true
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop(">", a1, a2) => 
     compile_aexp(a2, env) ++ compile_aexp(a1, env) ++ i"if_icmpge $jmp"
  case Bop("<=", a1, a2) =>
     compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case For(a1, a2, bl) => {
    val Assign(i, a) = a1
    compile_block(
      List(a1,
      While(Bop("<=", Var(i), a2), bl ++ List(Assign(i, Aop("+", Var(i), Num(1)))))),
      env)
  }
  case Write(x) => 
    (i"ldc ${x} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/writeString(Ljava/lang/String;)V", env)
  case WriteID(x) => 
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  case Read(x) => {
    val index = env.getOrElse(x, env.keys.size) 
    (i"invokestatic XXX/XXX/read()I" ++ 
     i"istore $index \t\t; $x", env + (x -> index))
  }
}

// compilation of a block (i.e. list of instructions)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

// main compilation function for blocks
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}


// compiling and running files
//
// JVM files can be assembled with 
//
//    java -jar jvm/jasmin-2.4/jasmin.jar fib.j
//
// and started with
//
//    java fib/fib



import scala.util._
import scala.sys.process._
import scala.io

def compile_tofile(bl: Block, class_name: String) = {
  val output = compile(bl, class_name)
  val fw = new java.io.FileWriter(class_name + ".j") 
  fw.write(output) 
  fw.close()
}

def compile_all(bl: Block, class_name: String) : Unit = {
  compile_tofile(bl, class_name)
  println("compiled ")
  val test = ("java -jar jvm/jasmin-2.4/jasmin.jar " + class_name + ".j").!!
  println("assembled ")
}

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


def compile_run(bl: Block, class_name: String) : Unit = {
  println("Start compilation")
  compile_all(bl, class_name)
  println("running")
  println("Time: " + time_needed(1, ("java " + class_name + "/" + class_name).!))
}

val fib = """write "Fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
temp := minus2;
minus2 := minus1 + minus2;
minus1 := temp;
n := n - 1
};
write "Result";
write minus2
"""
// compile_run(Block.parse_all(whileLex(fib)).head, "fib")

val fact = """write "Fact";
read n;
fact := 1;
i := 1;
while i <= n do {
fact := fact * i;
i := i + 1
};
write "Result";
write fact
"""

compile_run(Block.parse_all(whileLex(fact)).head, "fact")

val test = """if (2 <= 2) then {write "true"} else {write "wrong"}"""

// compile_run(Block.parse_all(whileLex(test)).head, "test")

val for_loop = """for i := 2 upto 4 do {
write i
}"""

// compile_run(Block.parse_all(whileLex(for_loop)).head, "for")


val q3 = """for i := 1 upto 10 do {
for i := 1 upto 10 do {
write i
}
}"""

// compile_run(Block.parse_all(whileLex(q3)).head, "q3")

