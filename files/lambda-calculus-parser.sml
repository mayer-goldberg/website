(* lambda.sml
 * Working with the lambda calculus in SML
 *
 * The important modules and procedures are
 * 
 * - len
 * - Parser
 * -- Parser.exprsToApplic
 * -- Parser.line
 * -- Parser.multiline
 * -- Parser.file
 * - Constants
 * 
 * Programmer: Mayer Goldberg, 2008
 *)

fun rel() = use "/Users/admin/gmayer/work/lang/ml/lambda.sml";

(* helper procedures *)

structure General = 
struct
fun andmap f nil = true
  | andmap f (a :: s) = (f a) andalso (andmap f s);

fun ormap f nil = false
  | ormap f (a :: s) = (f a) orelse (ormap f s);

fun makeIsChar(string) = 
    let val chars = explode(string)
    in
        fn ch => ormap (fn ch' => ch = ch') chars
    end;

fun makeCharInRange(charFrom, charTo) = 
    (fn ch : char => (charFrom <= ch) andalso (ch <= charTo));

fun stringEqual(string1, string2) = 
    String.compare(string1, string2) = EQUAL

fun iota from to f = 
    if from < to 
    then (f from) :: (iota (from + 1) to f)
    else [];

val ^^ = foldr (op ^) "";

fun fileToString (filename : string) =
    let val f = TextIO.openIn filename
        fun loop s = 
            (case TextIO.input1 f
              of NONE => s
               | SOME c => loop (c :: s))
        val result = String.implode (rev (loop []))
    in 
        TextIO.closeIn f;
        result
    end;

end; (* of structure General *)

(* Work on Scanner starts here *)

structure Scanner = 
struct 
open General;

datatype LCToken = LparenToken
                 | RparenToken
                 | LbrackToken
                 | RbrackToken
                 | CommaToken
                 | LambdaToken
                 | DotToken
                 | SymbolToken of string
                 | ChurchToken of int
                 | ProjToken of int * int;
         
exception BadChar of char;
exception CantConvertToNumber of string;

val whiteChar = makeIsChar(" \t\r\n");
val upperChar = makeCharInRange(#"A", #"Z");
val lowerChar = makeCharInRange(#"a", #"z");
val digitChar = makeCharInRange(#"0", #"9");
val specialSymbolChar = makeIsChar("!@$^*-_=+<>/?'");

local val delimChar = makeIsChar("()[]\\.,")
in
fun delimiterChar (ch) = 
    delimChar(ch) orelse
    whiteChar(ch)
end;

fun symbolChar (ch) = 
    lowerChar(ch) orelse 
    upperChar(ch) orelse
    digitChar(ch) orelse
    specialSymbolChar(ch);

local 
    fun stInit([]) = []
      | stInit(#";" :: s) = stComment(s)
      | stInit(#"(" :: s) = LparenToken :: stInit(s)
      | stInit(#")" :: s) = RparenToken :: stInit(s)
      | stInit(#"[" :: s) = LbrackToken :: stInit(s)
      | stInit(#"]" :: s) = RbrackToken :: stInit(s)
      | stInit(#".":: s) = DotToken :: stInit(s)
      | stInit(#"," :: s) = CommaToken :: stInit(s)
      | stInit(#"\\" :: s) = LambdaToken :: stInit(s)
      | stInit(ch :: s) = 
        if symbolChar(ch) then stSymbol(s, [ch])
        else if whiteChar(ch) then stInit(s)
        else raise BadChar(ch)
    and stSymbol([], chars) = symbolCharsToToken(chars) :: stInit([])
      | stSymbol(#"_" :: s, chars) = stProj(s, chars, [])
      | stSymbol(s as (ch :: s'), chars) = 
        if symbolChar(ch) then stSymbol(s', (ch :: chars))
        else symbolCharsToToken(chars) :: stInit(s)
    and stProj([], chars, chars') = 
        projCharsToToken(chars, chars') :: stInit([])
      | stProj(s as (ch :: s'), chars, chars') = 
        if digitChar(ch) then stProj(s', chars, ch :: chars')
        else if delimiterChar(ch) then 
            projCharsToToken(chars, chars') :: stInit(s)
        else stSymbol(s', ([ch] @ chars' @ [#"_"] @ chars))
    and stComment([]) = stInit([])
      | stComment(#"\n" :: s) = stInit(s)
      | stComment(ch :: s) = stComment(s)
    and symbolCharsToToken s = 
        let val symbolString = implode(rev s)
        in
            if (andmap digitChar s) then
                let val numberString = Int.fromString(symbolString)
                in
                    case (numberString) of
                        SOME(n) => ChurchToken(n)
                      | NONE => raise CantConvertToNumber(symbolString)
                end
            else SymbolToken(symbolString)
        end
    and projCharsToToken (chars, chars') = 
        let val charsString = implode (rev chars)
            val charsString' = implode (rev chars')
        in
            case (Int.fromString(charsString),
                  Int.fromString(charsString')) of
                (SOME(n), SOME(m)) => ProjToken(n, m)
              | _ => SymbolToken(charsString ^ "_" ^ charsString')
        end
in
fun stringToTokens (str : string) = stInit(explode(str))
end;

end; (* of structure Scanner *)

(* work on the parser starts here *)

datatype LCExpr = VarExpr of string
                | ApplicExpr of LCExpr * LCExpr
                | LambdaExpr of string * LCExpr;

fun len (VarExpr _) = 1
  | len (ApplicExpr (e1, e2)) = 1 + (len e1) + (len e2)
  | len (LambdaExpr (_, e)) = 1 + (len e);

structure Parser = 
struct
open General;
open Scanner;

local fun loop 0 = VarExpr("z")
        | loop n = ApplicExpr(VarExpr("s"), (loop (n - 1)))
in 
fun makeChurch n = 
    LambdaExpr("s", LambdaExpr("z", (loop n)))
end;

fun makeIndexedVar n = "x" ^ (Int.toString n);

exception InvalidProjection of int * int;

local fun loop i to j = 
          if (i > to) then VarExpr(makeIndexedVar j)
          else LambdaExpr(makeIndexedVar(i), (loop (i + 1) to j))
in
fun makeProj n m = 
    if (n >= m) then LambdaExpr("z", ApplicExpr(VarExpr("z"), (loop 1 n m)))
    else raise InvalidProjection(n, m)
end;

exception ExpectingRparen of LCToken list;
exception ExpectingRbrack of LCToken list;
exception NullApplication;
exception TokensLeft of LCExpr * (LCToken list);
exception NoExpr;
exception InvalidLambdaExpr;

fun exprsToApplic (expr :: exprs) = 
    foldl (fn (b, a) => ApplicExpr (a, b)) expr exprs
  | exprsToApplic [] = raise NullApplication;

fun makeNTupleMaker n = 
    let val names = iota 1 (n + 1) (fn n => "x" ^ (Int.toString n))
        val body = exprsToApplic (map VarExpr ("y" :: names))
    in 
        foldr (fn (var, body) => LambdaExpr(var, body))
              body
              (names @ ["y"])
    end;

fun exprsToNTuple exprs = 
    (foldl (fn (e1, e2) => ApplicExpr(e2, e1))
           (makeNTupleMaker (length exprs))
           exprs);

local fun getExpr [] retExprAndTokens retNone = retNone()
        | getExpr (ChurchToken(n) :: tokens) retExprAndTokens retNone = 
          retExprAndTokens ((makeChurch n), tokens)
        | getExpr (ProjToken(n, m) :: tokens) retExprAndTokens retNone = 
          retExprAndTokens ((makeProj n m), tokens)
        | getExpr (SymbolToken(name) :: tokens) retExprAndTokens retNone = 
          retExprAndTokens (VarExpr(name), tokens)
        | getExpr (LparenToken :: tokens) retExprAndTokens retNone =
          getExprs tokens 
                   (fn (exprs, (RparenToken :: tokens)) => 
                       retExprAndTokens ((exprsToApplic exprs), tokens)
                     | (exprs, tokens) => raise ExpectingRparen(tokens))
        | getExpr (LbrackToken :: tokens) retExprAndTokens retNone = 
          getNTuple tokens 
                    (fn (exprs, (RbrackToken :: tokens)) =>
                        retExprAndTokens ((exprsToNTuple exprs), tokens)
                      | (exprs, tokens) => raise ExpectingRbrack(tokens))
        | getExpr (LambdaToken :: tokens) retExprAndTokens retNone = 
          getVars tokens
                  (fn ((vars as (_ :: _)), (DotToken :: tokens)) => 
                      getExprs tokens
                              (fn (exprs, tokens) => 
                                  retExprAndTokens
                                      ((foldr (fn (var, body) =>
                                                  (LambdaExpr (var, body)))
                                              (exprsToApplic exprs)
                                              vars), 
                                       tokens))
                    | _ => raise InvalidLambdaExpr)
        | getExpr (RparenToken :: tokens) retExprAndTokens retNone = retNone()
        | getExpr (RbrackToken :: tokens) retExprAndTokens retNone = retNone()
        | getExpr (CommaToken :: tokens) retExprAndTokens retNone = retNone()
        | getExpr (DotToken :: tokens) retExprAndTokens retNone = retNone()
    and getExprs [] retExprsAndTokens = retExprsAndTokens ([], [])
      | getExprs tokens retExprsAndTokens = 
        getExpr tokens
                (fn (expr, tokens) =>
                    getExprs tokens
                             (fn (exprs, tokens) => 
                                 retExprsAndTokens ((expr :: exprs), tokens)))
                (fn () => retExprsAndTokens ([], tokens))
    and getNTuple tokens retNTupleAndTokens = 
        getExprs tokens
                 (fn (exprs, (CommaToken :: tokens)) =>
                     getNTuple tokens
                               (fn (exprs', tokens) => 
                                   retNTupleAndTokens 
                                       (((exprsToApplic exprs) :: exprs'),
                                        tokens))
                   | (exprs, (tokens as Rbrack :: _)) =>
                     retNTupleAndTokens ([(exprsToApplic exprs)], tokens)
                   | (exprs, tokens) => raise ExpectingRbrack(tokens))
    and getVars (SymbolToken(var) :: tokens) retVarsAndTokens = 
        getVars tokens (fn (vars, tokens) => 
                           retVarsAndTokens ((var :: vars), tokens))
      | getVars tokens retVarsAndTokens = retVarsAndTokens ([], tokens)
in
fun stringToExpr (str : string) = 
    getExprs (stringToTokens str) 
             (fn (exprs, tokens) =>
                 let val expr = exprsToApplic exprs
                 in
                     (case tokens
                       of [] => expr
                        | tokens => raise TokensLeft(expr, tokens))
                 end )

(* this is the intended interface to the parser *)
fun line s = stringToExpr s
and multiline s = line (General.^^ s)
and file filename = line (General.fileToString filename);

end;

end; (* of structure Parser *)

structure Constants = 
struct

val line = Parser.line;
val multiline = Parser.multiline;

(* Some well-known constants for "growing" larger expressions 
 * Defining constants normally requires an environment, but being in
 * the pure lambda-calculus, we simply abstract over the primitives
 * we need, and then apply to them. This is really the same as the 
 * macro-expansion of let-expressions
 *)

val succ = line "\\n s z.s(n s z)";

val add = Parser.exprsToApplic
              [line 
                   "\\ s+ a b . b s+ a",
               succ];

val mul = Parser.exprsToApplic
              [line "\\+ a b . b (+ a) 0",
               add];

val exp = line "\\* a b.b(* a)1";

val exp' = line "\\a b.b a ;; Church's definition"; 

val True = line "\\x y.x";

val False = line "\\x y.y";

val zero = Parser.exprsToApplic
               [line "\\false true n.n(\\x.false)true",
                False, 
                True];

val fact = Parser.exprsToApplic
               [multiline
                    ["\\s+ mul.",
                     "    \\n.2_2(n(\\p.[s+(2_1 p),",
                     "                   mul(2_1 p)(2_2 p)])",
                     "             [1,1])"],
                succ,
                mul
            ];

val ycurry = line "\\f.((\\x.f(x x))(\\x.f(x x)))";

(* Some well-known combinators *)

val i = line "\\x.x";

val k = line "\\x y.x";

val b = line "\\x y z.x(y z)";

val c = line "\\x y z.x z y";

val s = line "\\x y z.x z(y z)";

val j = line "\\x y z t.x y(x t z)";

end;

(* Work on the typesetter starts here *)
