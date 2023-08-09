(* int.sml
 * A toy interpreter for Scheme, written in Standard ML
 *
 * Programmer: Mayer Goldberg, 2008
 *
 * HOW TO USE THE INTERPRETERS
 * The interpreter defines a procedure eval : string -> string, 
 * which takes in input as a string of characters, and returns 
 * the output -- as a printed form, again, as a string of characters. 
 * For example, at the SML/NJ prompt type 
 * eval "(list (fact 5) (ack 2 2))"
 * and you will get back the string
 * "(120 7)"
 *)

fun rel() = use("/Users/admin/gmayer/work/lang/ml/int.sml");

structure GeneralPurpose = 
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
 fn ch : char => (charFrom <= ch) andalso (ch <= charTo);

fun stringEqual(string1, string2) = 
    String.compare(string1, string2) = EQUAL;

end; (* of structure GeneralPurpose *)

signature EXPRESSIONS = 
sig
    datatype Sexpr = Void
		   | Nil
		   | Pair of Sexpr * Sexpr
		   | Symbol of string
		   | String of string
		   | Number of int
		   | Bool of bool
		   | Char of char
		   | Closure of (string list) * Expr * (string -> Sexpr)
		   | ClosureOpt of (string list) * string 
				   * Expr * (string -> Sexpr)
		   | ClosureVar of string * Expr * (string -> Sexpr)
		   | Primitive of (Sexpr list -> Sexpr)
	 and Expr = Const of Sexpr
		  | Var of string
		  | If of Expr * Expr * Expr
		  | Abs of (string list) * Expr
		  | AbsOpt of (string list) * string * Expr
		  | AbsVar of string * Expr
		  | App of Expr * (Expr list);
	     
    val schemeListToML : Sexpr -> Sexpr list;
    val MLListToScheme : Sexpr list -> Sexpr;	
end; (* of signature EXPRESSIONS *)

structure Expressions : EXPRESSIONS = 
struct

datatype Sexpr = Void
	      | Nil
	      | Pair of Sexpr * Sexpr
	      | Symbol of string
	      | String of string
	      | Number of int
	      | Bool of bool
	      | Char of char
	      | Closure of (string list) * Expr * (string -> Sexpr)
	      | ClosureOpt of (string list) * string 
			      * Expr * (string -> Sexpr)
	      | ClosureVar of string * Expr * (string -> Sexpr)
	      | Primitive of (Sexpr list -> Sexpr)
     and Expr = Const of Sexpr
	      | Var of string
	      | If of Expr * Expr * Expr
	      | Abs of (string list) * Expr
	      | AbsOpt of (string list) * string * Expr
	      | AbsVar of string * Expr
	      | App of Expr * (Expr list);

exception NotAList of Sexpr;

fun schemeListToML Nil = []
  | schemeListToML (Pair(car, cdr)) = car :: (schemeListToML cdr)
  | schemeListToML e = raise NotAList(e);

fun MLListToScheme [] = Nil
  | MLListToScheme (a :: s) = Pair(a, (MLListToScheme s));

end; (* end of structure Expressions *)

signature READER = 
sig
    type SchemeToken;
    type Sexpr;
    val stringToTokens : string -> SchemeToken list;
    val stringToSexprs : string -> Sexpr list;
end; (* of signature READER *)

structure Reader : READER = 
struct

open GeneralPurpose;
open Expressions;

datatype SchemeToken = LparenToken
		     | RparenToken
		     | QuoteToken
		     | DotToken
		     | IntToken of int
		     | CharToken of char
		     | StringToken of string
		     | SymbolToken of string
		     | BoolToken of bool;

exception ErrorNothingAfterHash;
exception ErrorBadChar of char * string;
exception ErrorStringDoesntEnd of string;
exception ErrorNoMetaChar of string;
exception ErrorNoSuchMetaChar of string;
exception ErrorNoChar;
exception ErrorUnknownNamedChar of string;
exception ErrorHash of string;

val whiteChar = makeIsChar(" \t\r\n");
val delimiterChar = makeIsChar("'()\";, \t\r\n");
val octalChar = makeCharInRange(#"0", #"7");
val upperChar = makeCharInRange(#"A", #"Z");
val lowerChar = makeCharInRange(#"a", #"z");
val digitChar = makeCharInRange(#"0", #"9");
val specialSymbolChar = makeIsChar("!@$%^*-_=+<>/?.");

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
      | stInit(#"'" :: s) = QuoteToken :: stInit(s)
      | stInit(#"#" :: s) = stHash(s)
      | stInit(#"." :: s) = DotToken :: stInit(s)
      | stInit(#"\"" :: s) = stString(s, [])
      | stInit(ch :: s) = 
	if symbolChar(ch) then stSymbol(s, [ch])
	else if whiteChar(ch) then stInit(s)
	else raise ErrorBadChar(ch, implode(s))
    and stSymbol([], chars) = 
	symbolOrNumberToken(charsToString(chars)) :: stInit([])
      | stSymbol(s as char :: s', chars) = 
	if symbolChar(char) then stSymbol(s', char :: chars)
	else symbolOrNumberToken(charsToString(chars)) :: stInit(s)
    and stString([], chars) = 
	raise ErrorStringDoesntEnd(charsToString(chars))
      | stString(#"\"" :: s, chars) = 
	StringToken(charsToString(chars)) :: stInit(s)
      | stString(#"\\" :: s, chars) = stStringMetaChar(s, chars)
      | stString(ch :: s, chars) = stString(s, ch :: chars)
    and stStringMetaChar([], chars) = 
	raise ErrorNoMetaChar(charsToString(chars) ^ "\\")
      | stStringMetaChar(#"t" :: s, chars) = stString(s, #"\t" :: chars)
      | stStringMetaChar(#"T" :: s, chars) = stString(s, #"\t" :: chars)
      | stStringMetaChar(#"r" :: s, chars) = stString(s, #"\r" :: chars)
      | stStringMetaChar(#"R" :: s, chars) = stString(s, #"\r" :: chars)
      | stStringMetaChar(#"n" :: s, chars) = stString(s, #"\n" :: chars)
      | stStringMetaChar(#"N" :: s, chars) = stString(s, #"\n" :: chars)
      | stStringMetaChar(#"\\" :: s, chars) = stString(s, #"\\" :: chars)
      | stStringMetaChar(#"\"" :: s, chars) = stString(s, #"\"" :: chars)
      | stStringMetaChar(ch :: s, chars) = 
	raise ErrorNoSuchMetaChar("\\" ^ Char.toString(ch))
    and stHash([]) = raise ErrorNothingAfterHash
      | stHash(#"t" :: s) = BoolToken(true) :: stInit(s)
      | stHash(#"T" :: s) = BoolToken(true) :: stInit(s)
      | stHash(#"f" :: s) = BoolToken(false) :: stInit(s)
      | stHash(#"F" :: s) = BoolToken(false) :: stInit(s)
      | stHash(#"\\" :: s) = stChar(s)
      | stHash(s) = raise ErrorHash("#\\" ^ implode(s))
    and stChar([]) = raise ErrorNoChar
      | stChar(ch :: s) = stChar'(s, [ch])
    and stChar'([], chars) = makeCharToken(chars) :: stInit([])
      | stChar'(s as ch :: s', chars) = 
	if delimiterChar(ch) then makeCharToken(chars) :: stInit(s)
	else stChar'(s', ch :: chars)
    and stComment([]) = stInit([])
      | stComment(#"\n" :: s) = stInit(s)
      | stComment(ch :: s) = stComment(s)
    and charsToString(s) = implode(rev(s))
    and makeCharToken([ch]) = CharToken(ch)
      | makeCharToken(chars as [ch1, ch2, ch3]) = 
	if (andmap octalChar chars) then
	    CharToken(chr(digitToInt(ch1) + 
			  8 * (digitToInt(ch2) + 
			       8 * digitToInt(ch3))))
	else charNameToCharToken(charsToString(chars))
      | makeCharToken(chars) = charNameToCharToken(charsToString(chars))
    and charNameToCharToken(charName) = 
	if stringEqual(charName, "space") then CharToken(#" ")
	else if stringEqual(charName, "return") then CharToken(#"\r")
	else if stringEqual(charName, "newline") then CharToken(#"\n")
	else if stringEqual(charName, "tab") then CharToken(#"\t")
	else raise ErrorUnknownNamedChar(charName)
    and digitToInt(ch) = ord(ch) - ord(#"0")
    and symbolOrNumberToken(string) = 
	case Int.fromString(string) of
	    SOME (n) => IntToken(n)
	  | NONE => SymbolToken(string)
in
fun stringToTokens(string) = stInit(explode(string))
end;

exception ErrorNoSexprAfterQuote;
exception ErrorNoClosingLparen;
exception ErrorMissingSexprAfterDot;
exception ErrorInvalidPairSyntax;
exception ErrorCannotReadAllSexprs of (Sexpr list) * (SchemeToken list);
exception ErrorOnlyCombinesPairs of Sexpr;

fun getSexpr([], retSexprAndTokens, retNone) = retNone()
  | getSexpr(IntToken(value) :: tokens, retSexprAndTokens, retNone) = 
    retSexprAndTokens(Number(value), tokens)
  | getSexpr(BoolToken(value) :: tokens, retSexprAndTokens, retNone) = 
    retSexprAndTokens(Bool(value), tokens)
  | getSexpr(CharToken(value) :: tokens, retSexprAndTokens, retNone) =
    retSexprAndTokens(Char(value), tokens)
  | getSexpr(StringToken(value) :: tokens, retSexprAndTokens, retNone) = 
    retSexprAndTokens(String(value), tokens)
  | getSexpr(SymbolToken(value) :: tokens, retSexprAndTokens, retNone) = 
    retSexprAndTokens(Symbol(value), tokens)
  | getSexpr(QuoteToken :: tokens, retSexprAndTokens, retNone) = 
    getSexpr(tokens, 
	     (fn (e, tokens) =>
		 retSexprAndTokens(Pair(Symbol("quote"),
					Pair(e, Nil)), 
				   tokens)),
	     (fn () => raise ErrorNoSexprAfterQuote))
  | getSexpr(LparenToken :: tokens, retSexprAndTokens, retNone) =
    getSexprs(tokens,
	      (fn (es, []) => raise ErrorNoClosingLparen
		| (es, RparenToken :: tokens) =>
		  retSexprAndTokens(MLListToScheme(es), tokens)
		| (es, DotToken :: tokens) =>
		  getSexpr(tokens,
			   (fn (e, []) => raise ErrorNoClosingLparen
			     | (e, RparenToken :: tokens) =>
			       retSexprAndTokens(
			       combine(MLListToScheme(es), e),
			       tokens)
			     | (e, tokens) => 
			       raise ErrorNoClosingLparen),
			   (fn () => raise ErrorMissingSexprAfterDot))
		| (es, tokens) => raise ErrorInvalidPairSyntax))
  | getSexpr(RparenToken :: tokens, retSexprAndTokens, retNone) =
    retNone()
  | getSexpr(DotToken :: tokens, retSexprAndTokens, retNone) =
    retNone()
and getSexprs(tokens, retSexprsAndTokens) = 
    getSexpr(tokens,
	     (fn (e, tokens) =>
		 getSexprs(tokens,
			   (fn (es, tokens) =>
			       retSexprsAndTokens(e :: es, tokens)))),
	     (fn () => retSexprsAndTokens([], tokens)))
and combine(Nil, e) = e
  | combine(Pair(car, cdr), e) = 
    Pair(car, combine(cdr, e))
  | combine(someSexpr, e) = raise ErrorOnlyCombinesPairs(someSexpr)
and tokensToSexprs(tokens) = 
    getSexprs(tokens,
	      (fn (es, []) => es
		| (es, tokens) =>
		  raise ErrorCannotReadAllSexprs(es, tokens)))
and stringToSexprs(string) = 
    tokensToSexprs(stringToTokens string);
end; (* of structure Reader *)

signature TO_STRING = 
sig
    type Sexpr;
    val toString : Sexpr -> string;
end;

structure ToString : TO_STRING = 
struct
open GeneralPurpose;
open Expressions;

fun toString'(Void) = "#<void>"
  | toString'(Nil) = "()"
  | toString'(Number(n)) = Int.toString(n)
  | toString'(Char(#" ")) = "#\\space"
  | toString'(Char(#"\t")) = "#\\tab"
  | toString'(Char(#"\n")) = "#\\newline"
  | toString'(Char(#"\r")) = "#\\return"
  | toString'(Char(ch)) = 
    if (ch > #" ") then "#\\" ^ Char.toString(ch)
    else let val n = ord(ch)
	     val o3 = n mod 8
	     val tmp = n div 8
	     val o2 = tmp mod 8
	     val o1 = tmp div 8
	 in
	     "#\\" ^
	     Int.toString(o1) ^
	     Int.toString(o2) ^ 
	     Int.toString(o3)
	 end
  | toString'(Bool(true)) = "#t"
  | toString'(Bool(false)) = "#f"
  | toString'(String(str)) = "\"" ^ str ^ "\""
  | toString'(Symbol(name)) = name
  | toString'(Pair(Symbol("quote"),
		   Pair(e, Nil))) = "'" ^ toString'(e)
  | toString'(Pair(car, cdr)) = toStringWithCar(toString'(car), cdr)
  | toString'(Closure(_, _, _)) = "#<user-defined closure>"
  | toString'(ClosureOpt(_, _, _, _)) = "#<user-defined closure>"
  | toString'(ClosureVar(_, _, _)) = "#<user-defined closure>"
  | toString'(Primitive(_)) = "#<primitive procedure>"
and toStringWithCar(car, Nil) = "(" ^ car ^ ")"
  | toStringWithCar(car, Pair(first, second)) = 
    toStringWithCar(car ^ " " ^ toString'(first), second)
  | toStringWithCar(car, e) = "(" ^ car ^ " . " ^ toString'(e) ^ ")"
and toString(Void) = ""
  | toString(e) = toString'(e);

end; (* of struct ToString *)

signature ENVIRONMENT = 
sig
    type Sexpr;

    exception NotFound of string;
    exception UnequalVarsArgs;

    val env0 : string -> Sexpr;
    val extend : string list -> Sexpr list -> (string -> Sexpr) 
		 -> string -> Sexpr;
    val extendOpt : string list -> string -> Sexpr list -> (string -> Sexpr)
		    -> string -> Sexpr;
    val extendVar : string -> Sexpr list -> (string -> Sexpr) 
		    -> string -> Sexpr;
end;

structure Environment : ENVIRONMENT = 
struct

open GeneralPurpose;
open Expressions;

exception NotFound of string;
exception UnequalVarsArgs;

val env0 = (fn v => raise NotFound(v));

fun extend [] [] env = env
  | extend (name :: names) (value :: vals) env = 
    let val r = (extend names vals env)
    in 
	(fn v => if stringEqual(v, name) then value else (r v))
    end
  | extend _ _ _ = raise UnequalVarsArgs
and extendOpt [] opt vals env = 
    extend [opt] [(MLListToScheme vals)] env
  | extendOpt (var :: vars) opt (val' :: vals) env = 
    extend [var] [val'] (extendOpt vars opt vals env)
  | extendOpt _ _ _ _ = raise UnequalVarsArgs
and extendVar var vals env = extend [var] [(MLListToScheme vals)] env;

end; (* of structure Environment *)

signature TAG_PARSER = 
sig
    type Sexpr;
    type Expr;

    exception ErrorReservedWordUsedImproperly of string;
    exception ErrorMalformedLambdaArgList of string;
    exception UnrecognizedAST of Sexpr;
    exception NotASymbol of Sexpr;
	      
    val parseExpr : Sexpr -> Expr;
    val ast : string -> Expr;
end;

structure TagParser : TAG_PARSER = 
struct
open GeneralPurpose;
open Expressions;
open Reader;
open ToString;

exception ErrorReservedWordUsedImproperly of string;
exception ErrorMalformedLambdaArgList of string;
exception UnrecognizedAST of Sexpr;
exception NotASymbol of Sexpr;

val reservedSymbols = ["and", "begin", "cond", "define", "else", 
		       "if", "lambda", "let", "let*", "letrec", 
		       "or", "quote", "set!"]
fun reservedWord(str) = 
    ormap (fn rs => (String.compare(rs, str) = EQUAL)) reservedSymbols;

fun scmRdcAndRac(Nil, retRdcRac) = retRdcRac(Nil, Nil)
  | scmRdcAndRac(Pair(car, cdr), retRdcRac) = 
    scmRdcAndRac(cdr, (fn (rdc, rac) =>
			  retRdcRac(Pair(car, rdc), rac)))
  | scmRdcAndRac(e, retRdcRac) = retRdcRac(Nil, e);

fun parseExpr(Void) = Const(Void)
  | parseExpr(Nil) = Const(Nil)
  | parseExpr(e as Number(_)) = Const(e)
  | parseExpr(e as Char(_)) = Const(e)
  | parseExpr(e as Bool(_)) = Const(e)
  | parseExpr(e as String(_)) = Const(e)
  | parseExpr(Pair(Symbol("quote"),
		      Pair(e, Nil))) = Const(e)
  | parseExpr(Symbol(e)) =
    if reservedWord(e) then raise ErrorReservedWordUsedImproperly(e)
    else Var(e)
  | parseExpr(Pair(Symbol("if"),
		      Pair(test, 
			   Pair(dit, Nil)))) = 
    If(parseExpr(test), parseExpr(dit), Const(Void))
  | parseExpr(Pair(Symbol("if"),
		      Pair(test, 
			      Pair(dit, 
				      Pair(dif, Nil))))) = 
    If(parseExpr(test), parseExpr(dit), parseExpr(dif))
  | parseExpr(Pair(Symbol("lambda"),
		      (Pair(argl, (Pair(body, Nil)))))) = 
    scmRdcAndRac(argl,
		 (fn (rdc, Nil) =>
		     Abs((map (fn (Symbol str) => str 
				| e => raise NotASymbol(e))
			      (schemeListToML(rdc))), 
			  parseExpr(body))
		   | (Nil, Symbol(name)) =>
		     AbsVar(name, parseExpr(body))
		   | (rdc as Pair(_, _), Symbol(name)) =>
		     AbsOpt((map (fn (Symbol str) => str 
				   | e => raise NotASymbol(e))
				 (schemeListToML(rdc))), 
			    name, 
			    parseExpr(body))
		   | (rdc, rac) => 
		     raise ErrorMalformedLambdaArgList(toString argl)))
  | parseExpr (e as Pair(p, q)) = 
    scmRdcAndRac(q, (fn (rdc, Nil) =>
			App(parseExpr(p), map parseExpr(schemeListToML(rdc)))
		      | _ => raise UnrecognizedAST(e)))
  | parseExpr e = raise UnrecognizedAST(e);

fun asts string = map parseExpr (stringToSexprs string);

fun ast string = hd(asts string);
end; (* of structure TagParser *)

signature EVALUATOR = 
sig
    type Sexpr;
    type Expr;
    exception NotAProcedure of Sexpr;
    val ev : Expr -> (string -> Sexpr) -> Sexpr;
    val applyProc : Sexpr -> Sexpr list -> Sexpr;
end;

structure Evaluator : EVALUATOR =
struct

open GeneralPurpose;
open Expressions;
open Environment;

exception NotAProcedure of Sexpr;

fun ev (Const c) env = c
  | ev (Var str) env = (env str)
  | ev (If(test, dit, dif)) env = 
    (case (ev test env) of
	 Bool(false) => (ev dif env)
       | _ => (ev dit env))
  | ev (Abs(vars, body)) env = Closure(vars, body, env)
  | ev (AbsOpt(vars, opt, body)) env = ClosureOpt(vars, opt, body, env)
  | ev (AbsVar(var, body)) env = ClosureVar(var, body, env)
  | ev (App(proc, args)) env = 
    let val p = ev proc env
	val vals = map (fn e => ev e env) args
    in
	applyProc p vals
    end
and applyProc (Closure(vars, body, env)) vals = 
    (ev body (extend vars vals env))
  | applyProc (ClosureOpt(vars, opt, body, env)) vals = 
    (ev body (extendOpt vars opt vals env))
  | applyProc (ClosureVar(var, body, env)) vals = 
    (ev body (extendVar var vals env))
  | applyProc (Primitive(proc)) vals = proc(vals)
  | applyProc e vals = raise NotAProcedure(e);

end; (* end of structure Evaluator *)

signature PRIMITIVE_FUNCTIONS = 
sig
    type Sexpr;

    exception InvalidArglist;
    exception NotANumber;
    exception BadArgl of Sexpr list;

    val addPrimitives : (string * (Sexpr list -> Sexpr)) list
                        -> (string -> Sexpr) -> string -> Sexpr;
    val primAdd : Sexpr list -> Sexpr;
    val primSub : Sexpr list -> Sexpr;
    val primMul : Sexpr list -> Sexpr;
    val primApply : Sexpr list -> Sexpr;
    val primCons : Sexpr list -> Sexpr;
    val primCar : Sexpr list -> Sexpr;
    val primCdr : Sexpr list -> Sexpr;
    val primNumber : Sexpr list -> Sexpr;
    val primString : Sexpr list -> Sexpr;
    val primSymbol : Sexpr list -> Sexpr;
    val primBool : Sexpr list -> Sexpr;
    val primNull : Sexpr list -> Sexpr;
    val primChar : Sexpr list -> Sexpr;
    val primProcedure : Sexpr list -> Sexpr;
    val primZero : Sexpr list -> Sexpr;
    val primNumLt : Sexpr list -> Sexpr;
    val primNumEq : Sexpr list -> Sexpr;
    val primNumGt : Sexpr list -> Sexpr;
    val primSymbolToString : Sexpr list -> Sexpr;
    val primStringToSymbol : Sexpr list -> Sexpr;
    val primStringToList : Sexpr list -> Sexpr;
    val primListToString : Sexpr list -> Sexpr;
    val primBinaryStringAppend : Sexpr list -> Sexpr;
end;

structure PrimitiveFunctions : PRIMITIVE_FUNCTIONS = 
struct

open GeneralPurpose;
open Expressions;
open Environment;
open Evaluator;

exception InvalidArglist;
exception NotANumber;
exception NotAList of Sexpr;
exception BadArgl of Sexpr list;

fun addPrimitives [] env = env
  | addPrimitives ((primName, primFunc) :: prims) env = 
    extend [primName] [(Primitive primFunc)] (addPrimitives prims env);

fun primAdd(s) = 
    Number(foldr (op +) 0
		 (map (fn (Number n) => n 
			| _ => raise NotANumber) 
		      s));

(* !!! make primSub variadic! *)
fun primSub([(Number a), (Number b)]) = Number(a - b)
  | primSub _ = raise InvalidArglist;

fun primMul(s) =
    Number(foldr (op * ) 1
		      (map (fn (Number n) => n 
			     | _ => raise NotANumber) 
			   s));

fun primApply([proc, s]) = applyProc proc (schemeListToML s)
  | primApply argl = raise BadArgl(argl);

fun primCons([sexpr1, sexpr2]) = Pair(sexpr1, sexpr2)
  | primCons argl = raise BadArgl(argl);

fun primCar([Pair(car, _)]) = car
  | primCar e = raise BadArgl(e);

fun primCdr([Pair(_, cdr)]) = cdr
  | primCdr e = raise BadArgl(e);

fun primNumber([Number(_)]) = Bool(true)
  | primNumber ([e]) = Bool(false)
  | primNumber e = raise BadArgl(e);

fun primString([String(_)]) = Bool(true)
  | primString ([e]) = Bool(false)
  | primString e = raise BadArgl(e);

fun primSymbol([Symbol(_)]) = Bool(true)
  | primSymbol ([e]) = Bool(false)
  | primSymbol e = raise BadArgl(e);

fun primBool([Bool(_)]) = Bool(true)
  | primBool ([e]) = Bool(false)
  | primBool e = raise BadArgl(e);

fun primNull([Nil]) = Bool(true)
  | primNull ([e]) = Bool(false)
  | primNull e = raise BadArgl(e);

fun primChar([Char(_)]) = Bool(true)
  | primChar([e]) = Bool(false)
  | primChar e = raise BadArgl(e);

fun primProcedure([Closure(_, _, _)]) = Bool(true)
  | primProcedure([Primitive(_)]) = Bool(true)
  | primProcedure ([e]) = Bool(false)
  | primProcedure e = raise BadArgl(e);

fun primZero([Number(0)]) = Bool(true)
  | primZero([Number(_)]) = Bool(false)
  | primZero(e) = raise BadArgl(e);

fun makeNumComparisons(compare) = 
    (fn [(Number a), (Number b)] => Bool(compare(a, b))
      | e => raise BadArgl(e));

val primNumLt = makeNumComparisons(op <);
val primNumEq = makeNumComparisons(op =);
val primNumGt = makeNumComparisons(op >);

fun primStringToSymbol([String str]) = (Symbol str)
  | primStringToSymbol e = raise (BadArgl e);

fun primSymbolToString([Symbol str]) = (String str)
  | primSymbolToString e = raise (BadArgl e);

fun primListToString([ss as Pair(_, _)]) = 
		     let val argl = (schemeListToML ss)
			 val str = (implode
					(map (fn (Char c) => c
					       | e => raise (BadArgl argl))
					     argl))
		     in (String str) end
  | primListToString e = raise (BadArgl e);

fun primStringToList([String(str)]) = (MLListToScheme (map Char (explode str)))
  | primStringToList e = raise (BadArgl e);

fun primBinaryStringAppend([(String str1), (String str2)]) = 
    (String (str1 ^ str2))
  | primBinaryStringAppend e = raise (BadArgl e);

end; (* of structure PrimitiveFunctions *)

signature BUILTIN_FUNCTIONS = 
sig
    type Sexpr;
    type Expr;

    val builtinMap : Expr;
    val builtinY : Expr;
    val builtinFact : Expr;
    val builtinLength : Expr;
    val builtinWith : Expr;
    val builtinCompose : Expr;
    val builtinCaar : Expr; 
    val builtinCadr : Expr; 
    val builtinCdar : Expr; 
    val builtinCddr : Expr; 
    val builtinCaaar : Expr; 
    val builtinCaadr : Expr; 
    val builtinCadar : Expr; 
    val builtinCaddr : Expr; 
    val builtinCdaar : Expr; 
    val builtinCdadr : Expr; 
    val builtinCddar : Expr; 
    val builtinCdddr : Expr; 
    val builtinAck : Expr;
    val builtinList : Expr;
    val builtinNot : Expr;
    val builtinNumLe : Expr;
    val builtinNumGe : Expr;
    val builtinAppend : Expr;
    val builtinStringAppend : Expr;
end;

structure BuiltinFunctions : BUILTIN_FUNCTIONS = 
struct

open Expressions;
open TagParser;

val builtinMap = 
    ast ("((lambda (y)" ^
	 "   ((lambda (map1)" ^
	 "      ((lambda (maplist)" ^
	 "         (lambda (f . s)" ^
	 "           (maplist f s)))" ^
	 "       (y (lambda (maplist)" ^
	 "            (lambda (f s)" ^
	 "              (if (null? (car s)) '()" ^
	 "                  (cons (apply f (map1 car s))" ^
	 "                        (maplist f (map1 cdr s)))))))))" ^
	 "    (y (lambda (map1)" ^
	 "         (lambda (f s)" ^
	 "           (if (null? s) '()" ^
	 "               (cons (f (car s))" ^
	 "                     (map1 f (cdr s)))))))))" ^
	 " (lambda (f)" ^
	 "   ((lambda (x)" ^
	 "      (f (lambda args" ^
	 "           (apply (x x) args))))" ^
	 "    (lambda (x)" ^
	 "      (f (lambda args" ^
	 "           (apply (x x) args)))))))");

val builtinY = 
    ast ("(lambda fs" ^
	 "  ((lambda (ms) (apply (car ms) ms))" ^
	 "   (map" ^
	 "     (lambda (fi)" ^
	 "       (lambda ms" ^
	 "         (apply fi (map (lambda (mi)" ^
	 "                          (lambda args" ^
	 "                            (apply (apply mi ms) args))) ms))))" ^
	 "     fs)))");

val builtinFact = 
    ast ("(y (lambda (fact)" ^
	 "     (lambda (n)" ^
	 "       (if (zero? n) 1" ^
	 "         (* n (fact (- n 1)))))))");

val builtinLength = 
    ast ("(y (lambda (length)" ^
	 "     (lambda (s)" ^
	 "       (if (null? s) 0" ^
	 "         (+ 1 (length (cdr s)))))))");

val builtinCompose = 
    ast ("((lambda (compose-list) (lambda fs (compose-list fs)))" ^
	 " (y (lambda (compose-list)" ^
	 "      (lambda (s)" ^
	 "        (if (null? s) (lambda (x) x)" ^
	 "          ((lambda (f g) (lambda (x) (f (g x))))" ^
	 "           (car s)" ^
	 "           (compose-list (cdr s))))))))");

val builtinWith = ast "(lambda (s f) (apply f s))";

val builtinCaar = ast "(compose car car)";
val builtinCadr = ast "(compose car cdr)";
val builtinCdar = ast "(compose cdr car)";
val builtinCddr = ast "(compose cdr cdr)";
val builtinCaaar = ast "(compose car car car)";
val builtinCaadr = ast "(compose car car cdr)";
val builtinCadar = ast "(compose car cdr car)";
val builtinCaddr = ast "(compose car cdr cdr)";
val builtinCdaar = ast "(compose cdr car car)";
val builtinCdadr = ast "(compose cdr car cdr)";
val builtinCddar = ast "(compose cdr cdr car)";
val builtinCdddr = ast "(compose cdr cdr cdr)";

val builtinAck =
    ast ("(y (lambda (ack)" ^
	 "     (lambda (a b)" ^
	 "       (if (zero? a) (+ b 1)" ^
	 "         (if (zero? b) (ack (- a 1) 1)" ^
	 "           (ack (- a 1) (ack a (- b 1))))))))");

val builtinList = ast "(lambda args args)";

val builtinNot = ast "(lambda (e) (if e #f #t))";

val builtinNumLe = ast "(lambda (a b) (not (> a b)))";
val builtinNumGe = ast "(lambda (a b) (not (< a b)))";

val builtinAppend = 
    ast ("((lambda (binary-append)" ^
	 "   ((lambda (append-list)" ^
	 "      (lambda args" ^
	 "        (append-list args)))" ^
	 "    (y (lambda (append-list)" ^
	 "         (lambda (s)" ^
	 "           (if (null? s) '()" ^
	 "               (binary-append (car s)" ^
	 "                 (append-list (cdr s)))))))))" ^
	 " (y (lambda (binary-append)" ^
	 "      (lambda (s1 s2)" ^
	 "        (if (null? s1) s2" ^
	 "            (cons (car s1)" ^
	 "                  (binary-append (cdr s1) s2)))))))");

val builtinStringAppend =
    ast ("((lambda (string-append-list)" ^
	 "   (lambda strings" ^
	 "     (string-append-list strings)))" ^
	 " (y (lambda (string-append-list)" ^
	 "      (lambda (s)" ^
	 "        (if (null? s) \"\"" ^
	 "            (binary-string-append (car s)" ^
	 "             (string-append-list (cdr s))))))))");

end; (* of structure BuiltinFunctions *)

signature INITIAL_ENVIRONMENT = 
sig
    type Sexpr;

    val envInit : string -> Sexpr
end;

structure InitialEnvironment : INITIAL_ENVIRONMENT =
struct

open Environment;
open Evaluator;
open PrimitiveFunctions;
open BuiltinFunctions;

fun addBuiltins [] env = env
  | addBuiltins ((name, ast) :: rest) env = 
    addBuiltins rest (extend [name] [(ev ast env)] env);

val envInit = 
    addBuiltins 
	[("map", builtinMap),
	 ("y", builtinY),
	 ("fact", builtinFact),
	 ("length", builtinLength),
	 ("with", builtinWith),
	 ("ack", builtinAck),
	 ("list", builtinList),
	 ("compose", builtinCompose),
	 ("caar", builtinCaar),
	 ("caar", builtinCaar),
	 ("cadr", builtinCaar),
	 ("cdar", builtinCaar),
	 ("cddr", builtinCaar),
	 ("caaar", builtinCaaar),
	 ("caadr", builtinCaadr),
	 ("cadar", builtinCadar),
	 ("caddr", builtinCaddr),
	 ("cdaar", builtinCdaar),
	 ("cdadr", builtinCdadr),
	 ("cddar", builtinCddar),
	 ("cdddr", builtinCdddr),
	 ("not", builtinNot),
	 ("<=", builtinNumLe),
	 (">=", builtinNumGe),
	 ("append", builtinAppend),
	 ("string-append", builtinStringAppend)]
	(addPrimitives 
	     [("+", primAdd), 
	      ("*", primMul),
	      ("-", primSub), 
	      ("apply", primApply),
	      ("boolean?", primBool),
	      ("car", primCar),
	      ("cdr", primCdr),
	      ("char?", primChar),
	      ("cons", primCons),
	      ("null?", primNull),
	      ("number?", primNumber),
	      ("procedure?", primProcedure),
	      ("string?", primString),
	      ("symbol?", primSymbol),
	      ("zero?", primZero),
	      ("<", primNumLt),
	      ("=", primNumEq),
	      (">", primNumGt),
	      ("symbol->string", primSymbolToString),
	      ("string->symbol", primStringToSymbol),
	      ("string->list", primStringToList),
	      ("list->string", primListToString),
	      ("binary-string-append", primBinaryStringAppend)] 
	     env0);
    
end; (* of structure InitialEnvironment *)

