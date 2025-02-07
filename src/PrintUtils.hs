module PrintUtils where
import VMTypes
import TCTypes
import Syntax.Abs (Type (..), TypeNoref (..), TypeRef (..), CIdent (..), TClean (..), TFuns (..), TComp (..), TPrim (..), TInt (..))

toString :: Value -> String

toString (Vint (i, v)) = show i
toString Vvoid = "__void__"
toString (Vbool b) = show b
toString (Vchar c) = [c]
toString (Vstr s) = s
toString (Varr arr) = "[" ++ printList (map toString arr) ++ "]"
toString (Vtup tup) = "(" ++ printList (map toString tup) ++ ")"
toString (Vfun _) = "__function__"
toString (Ref loc) = "reference to #" ++ show loc

printList :: [String] -> String
printList l = case l of
    [] -> ""
    [v] -> v
    (v:t) -> v ++ ", " ++ printList t

printDiag :: Diag -> String
printDiag (Err err) = "[Error] " ++ printErr err
printDiag (Warn warn) = "[Warning] " ++ printWarn warn

printCodePos :: CodePos -> String
printCodePos (row, col) = "line " ++ show row ++ ", column " ++ show col

printErr :: Error -> String
printErr DivZero = "Cannot divide by 0."
printErr ModZero = "Cannot take modulo 0."
printErr (UseUninit loc) =
    "Cannot use uninitialized variable stored at location #" ++ show loc ++ "."
printErr (VMTypes.Undeclared pos s) =
    "Cannot use undeclared variable `" ++ s ++
    "` at " ++ printCodePos pos ++ "."
printErr (CharOutOfBounds i) =
    "Cannot convert number " ++ show i ++ " to character."
printErr (ArrOutOfBounds i len) =
    "Index " ++ show i ++ " out of expected range [0, " ++ show len ++ "]."
printErr (PopEmpty pos arrName) =
    "Cannot use `.pop()` on empty array `" ++ arrName ++
    "` at " ++ printCodePos pos ++ "."
printErr (NegativeSize pos arrName) =
    "Cannot set a negative size of array `" ++ arrName ++
    "` at " ++ printCodePos pos ++ "."
printErr (AssertionFailed msg) =
    "Assertion failed: " ++ msg
printErr (UncaughtReturnValue ret) =
    "Cannot use `return` statement outside of a function body. " ++
    "Incorrectly returned value: " ++ toString ret ++ "."
printErr PanicUnexpectedType =
    "This is an internal bug. You should not see this. We're sorry."

printIntLossReason :: IntLossReason -> String
printIntLossReason reason = case reason of
    Conversion -> "conversion"
    Arithmetic -> "arithmetic operation"
    Literal -> "literal out of accepted i64 bounds"

printWarn :: Warning -> String
printWarn (IntLoss reason before after) =
    "Integer loss occured from " ++ show before ++ " to " ++ show after ++
    ". Reason: " ++ printIntLossReason reason ++ "."

printTCDiag :: TCDiag -> String
printTCDiag (TCWarn w) = "[Warning] " ++ printTCWarn w
printTCDiag (TCErr e) = "[Error] " ++ printTCErr e

printTCErr :: TCError -> String
printTCErr (TypeMismatch expected provided) =
    "Type mismatch occured. Expected type " ++ printType expected ++
    ", instead provided " ++ printType provided ++ "."
printTCErr (PlusMismatch t1 t2) =
    "Cannot use `+` with types: " ++ printType t1 ++ ", " ++ printType t2 ++
    ". The `+` operator only accepts the following type pairs:\n" ++
    "- (integer, integer) if both types are equal,\n" ++
    "- (char, integer) in this order."
printTCErr (MinusMismatch t1 t2) =
    "Cannot use `-` with types: " ++ printType t1 ++ ", " ++ printType t2 ++
    ". The `-` operator only accepts the following type pairs:\n" ++
    "- (integer, integer) if both types are equal,\n" ++
    "- (char, char),\n" ++
    "- (char, integer) in this order."
printTCErr (ExpectedInteger t) =
    "Only integer types can be used in this context. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr (ExpectedSigned t) =
    "Only signed integer types can be used in this context. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr (ExpectedOrdering t) =
    "Only types with ordering (integer, char) can be used in this context. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr (ExpectedArr t) =
    "Only arrays (`[element_type]`) can be used in this context. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr (SizeIsI64 t) =
    "The only accepted size type is `i64`. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr (ExpectedFun t) =
    "Only functions can be used in this context. " ++
    "Instead, provided " ++ printType t ++ "."
printTCErr InvalidTupleSize =
    "Tuples must contain at least two elements. Instead, provided just one."
printTCErr TupleUnpackingMismatch = 
    "Cannot unpack tuple into provided variables."
printTCErr (UnpackedRefTuple t) = 
    "Cannot unpack a referenced type. Tried to unpack " ++ printType t ++ "."
printTCErr (UndeclaredVar pos name) =
    "Cannot use undeclared variable `" ++ name ++
    "` at " ++ printCodePos pos ++ "."
printTCErr (UndeclaredAlias pos name) =
    "Cannot use undeclared type alias `" ++ name ++
    "` at " ++ printCodePos pos ++ "."
printTCErr (AliasShadowing pos name) =
    "Cannot shadow type aliases. Type alias `" ++ name ++
    "` declared at " ++ printCodePos pos ++ " was declared previously."
printTCErr (ConstViolation t) =
    "Cannot mutate variables of type " ++ printType t ++ "."
printTCErr (InvalidCast to from) =
    "Cannot cast from " ++ printType from ++ " to " ++ printType to ++ "."
printTCErr UncaughtReturn =
    "Cannot use `return` statement outside of a function body."
printTCErr (UninitRef t) = 
    "Reference cannot be uninitialized. " ++
    "Tried to declare an uninitialized variable of type " ++ printType t ++ "."
printTCErr ArrayLvalue = 
    "Cannot use indexed array as an lvalue in a declaration."
printTCErr NoReturn =
    "Function has to return a value in every branch."
printTCErr EmptyArray =
    "You have to specify a type of an empty array using `<type>[]`."
printTCErr DifferentArrayTypes = 
    "All elements in an array must have the same type. " ++
    "Instead, provided different types in an array constructor."

printTCWarn :: TCWarning -> String
printTCWarn (Shadowing pos name) =
    "Declaration of `" ++ name  ++ "` at " ++ printCodePos pos ++
    " shadows a previously declared variable of the same type."

printTCWarn (UnusedReturn pos name) =
    "Return value of a function `" ++ name ++ "` called at " ++ printCodePos pos ++
    " is not used."

printTCWarn DeadCode = 
    "There is a dead code somewhere (code after return statement).";

---------- Type printing ---------- 
printType :: Type -> String
printType t = "`" ++ printTypeRaw t ++ "`"

printTypeRaw :: Type -> String
printTypeRaw (TNoref (Tclean t)) = printTypeClean t
printTypeRaw (TNoref (Tconst t)) = "const " ++ printTypeClean t
printTypeRaw (TRef (Tref t)) = "ref " ++ printTypeClean t
printTypeRaw (TRef (Tcref t)) = "cref " ++ printTypeClean t

printTypeClean :: TClean -> String
printTypeClean (Talias (CIdent (pos, name))) = name
printTypeClean (Tcomp t) = printTypeComp t

printTypeComp :: TComp -> String
printTypeComp (Tarr tel) = "[" ++ printTypeRaw tel ++ "]"
printTypeComp Tstr = "string"
printTypeComp (Ttup t1 tt) =
    "(" ++ printList (map printTypeRaw (t1:tt)) ++ ")"
-- Functions
printTypeComp (Tfun (TFun targ tret)) =
    "(" ++ printTypeRaw targ ++ " -> " ++
    printTypeRaw tret ++ ")"
-- Primary types
printTypeComp (Tprim t) = printTypePrim t

printTypePrim :: TPrim -> String
printTypePrim Tvoid = "void"
printTypePrim Tbool = "bool"
printTypePrim Tchar = "char"
printTypePrim (Tint Ti32) = "i32"
printTypePrim (Tint Ti64) = "i64"
printTypePrim (Tint Tu32) = "u32"
printTypePrim (Tint Tu64) = "u64"
