{-# LANGUAGE OverloadedStrings #-}
module Generate.Name.Expression
  ( generate
  , generateCtor
  , generateField
  , generateTailDef
  , generateMain
  , Code
  , codeToExpr
  , codeToStmtList
  )
  where


import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Map ((!))
import qualified Data.Map as Map
import qualified Data.Text.Encoding as Text

import qualified AST.Canonical as Can
import qualified AST.Optimized as Opt
import qualified AST.Module.Name as ModuleName
import qualified Data.Index as Index
import qualified Elm.Compiler.Type as Type
import qualified Elm.Compiler.Type.Extract as Extract
import qualified Elm.Name as N
import qualified Elm.Package as Pkg
import qualified Elm.Compiler.Version as Version
import qualified Generate.Lambda.Builder as L
import qualified Generate.Lambda.Mode as Mode
import qualified Generate.Lambda.Name as Name
import qualified Lamon.Encode as Encode
import qualified Optimize.DecisionTree as DT
import qualified Reporting.Region as R



-- EXPRESSIONS


generateLamExpr :: Mode.Mode -> Opt.Expr -> L.Expr
generateLamExpr mode expression =
  codeToExpr (generate mode expression)


generate :: Mode.Mode -> Opt.Expr -> Code
generate mode expression =
  case expression of
    Opt.Bool bool ->
      L.Var if bool
        then "True"
        else "False"

    Opt.Chr char ->
      L.Str (Text.encodeUtf8Builder char)

    Opt.Str string ->
      L.Str (Text.encodeUtf8Builder string)

    Opt.Int int ->
      L.Int int

    Opt.Float float ->
      L.Dec float

    Opt.VarLocal name ->
      L.Var (Name.fromLocal name)

    Opt.VarGlobal (Opt.Global home name) ->
      L.Var (Name.fromGlobal home name)

    Opt.VarEnum (Opt.Global home name) index ->
      case mode of
        Mode.Dev _ _ ->
          L.Var (Name.fromGlobal home name)

        Mode.Prod _ _ ->
          L.Int (Index.toMachine index)

    Opt.VarBox (Opt.Global home name) ->
      L.Var $
        case mode of
          Mode.Dev _ _ -> Name.fromGlobal home name
          Mode.Prod _ _ -> Name.fromGlobal ModuleName.basics N.identity

    Opt.VarCycle home name ->
      L.Lam (L.Var (Name.fromCycle home name)) [] -- TODO

    Opt.VarDebug name home region unhandledValueName ->
      generateDebug name home region unhandledValueName -- TODO

    Opt.VarKernel home name ->
      L.Var (Name.fromKernel home name)

    Opt.List entries ->
      generateList $ map (generateLamExpr mode) entries        

    Opt.Function args body ->
      generateFunction (map Name.fromLocal args) (generate mode body)

    Opt.Call func args ->
      generateCall mode func args

    Opt.TailCall name args ->
      generateTailCall mode name args

    Opt.If branches final ->
      generateIf mode branches final

    Opt.Let def body ->
      generateDef mode def : codeToStmtList (generate mode body)

    Opt.Destruct (Opt.Destructor name path) body ->
      let
        pathExpr = generatePath mode path
        pathDef = L.Var [ (Name.fromLocal name, Just pathExpr) ]
      in
      pathDef : codeToStmtList (generate mode body)

    Opt.Case label root decider jumps ->
      generateCase mode label root decider jumps

    Opt.Accessor field -> --TODO
      L.Lam Nothing [Name.dollar]
        [ L.Return $ Just $
            L.Access (L.Ref Name.dollar) (generateField mode field)
        ]

    Opt.Access record field ->
      LamExpr $ L.Access (generateLamExpr mode record) (generateField mode field)

    Opt.Update record fields ->
      L.Call (L.Ref (Name.fromKernel N.utils "update"))
        [ generateLamExpr mode record
        , generateRecord mode fields
        ]

    Opt.Record fields ->
      generateRecord mode fields

    Opt.Unit ->
      case mode of
        Mode.Dev _ _ ->
          L.Var (Name.fromKernel N.utils "Tuple0")

        Mode.Prod _ _ ->
          L.Int 0

    Opt.Tuple a b maybeC ->
      case maybeC of
        Nothing ->
          L.Lam (L.Var (Name.fromKernel N.utils "Tuple2"))
            [ generateLamExpr mode a
            , generateLamExpr mode b
            ]

        Just c ->
          L.Call (L.Ref (Name.fromKernel N.utils "Tuple3"))
            [ generateLamExpr mode a
            , generateLamExpr mode b
            , generateLamExpr mode c
            ]

    Opt.Shader src ->
      generateObject [ ( Name.fromLocal "src", L.Str (Text.encodeUtf8Builder src) ) ]

-- LIST
generateList = 
  foldr con nil 

con a b = 
  L.App L.SameLine (L.App L.SameLine (Lam.Var "Con") a) b

nil = L.Var "Nil"

-- CTOR
generateCtor :: Mode.Mode -> Opt.Global -> Index.ZeroBased -> Int -> L.Expr
generateCtor mode (Opt.Global home name) index arity =
  let
    argNames =
      Index.indexedMap (\i _ -> Name.fromIndex i) [1 .. arity]

    ctorTag =
      case mode of
        Mode.Dev _ _ -> L.String (N.toBuilder name)
        Mode.Prod _ _ -> L.Int (ctorToInt home name index)
  in
  generateFunction argNames $ LamExpr $ L.Object $
    (Name.dollar, ctorTag) : map (\n -> (n, L.Ref n)) argNames


ctorToInt :: ModuleName.Canonical -> N.Name -> Index.ZeroBased -> Int
ctorToInt home name index =
  if home == ModuleName.dict && name == "RBNode_elm_builtin" || name == "RBEmpty_elm_builtin" then
    0 - Index.toHuman index
  else
    Index.toMachine index



-- RECORDS
generateRecord :: Mode.Mode -> Map.Map N.Name Opt.Expr -> L.Expr
generateRecord mode fields =
  let
    toPair (field, value) =
      (generateField mode field, generateLamExpr mode value)
  in
  L.Object (map toPair (Map.toList fields))


generateField :: Mode.Mode -> N.Name -> Name.Name
generateField mode name =
  case mode of
    Mode.Dev _ _ ->
      Name.fromLocal name

    Mode.Prod _ fields ->
      fields ! name




-- DEBUG


generateDebug :: N.Name -> ModuleName.Canonical -> R.Region -> Maybe N.Name -> L.Expr
generateDebug name (ModuleName.Canonical _ home) region unhandledValueName =
  if name /= "todo" then
    L.Ref (Name.fromGlobal ModuleName.debug name)
  else
    case unhandledValueName of
      Nothing ->
        L.Call (L.Ref (Name.fromKernel N.debug "todo")) $
          [ L.String (N.toBuilder home)
          , regionToLamExpr region
          ]

      Just valueName ->
        L.Call (L.Ref (Name.fromKernel N.debug "todoCase")) $
          [ L.String (N.toBuilder home)
          , regionToLamExpr region
          , L.Ref (Name.fromLocal valueName)
          ]


regionToLamExpr :: R.Region -> L.Expr
regionToLamExpr (R.Region start end) =
  L.Object
    [ ( Name.fromLocal "start", positionToLamExpr start )
    , ( Name.fromLocal "end", positionToLamExpr end )
    ]


positionToLamExpr :: R.Position -> L.Expr
positionToLamExpr (R.Position line column) =
  L.Object
    [ ( Name.fromLocal "line", L.Int line )
    , ( Name.fromLocal "column", L.Int column )
    ]



-- FUNCTION


generateFunction :: [Name.Name] -> Code -> Code
generateFunction args body =
  case IntMap.lookup (length args) funcHelpers of
    Just helper ->
      LamExpr $
        L.Call helper
          [ L.Function Nothing args $
              codeToStmtList body
          ]

    Nothing ->
      let
        addArg arg code =
          LamExpr $ L.Function Nothing [arg] $
            codeToStmtList code
      in
      foldr addArg body args


{-# NOINLINE funcHelpers #-}
funcHelpers :: IntMap.IntMap L.Expr
funcHelpers =
  IntMap.fromList $
    map (\n -> (n, L.Ref (Name.makeF n))) [2..9]



-- CALLS


generateCall :: Mode.Mode -> Opt.Expr -> [Opt.Expr] -> L.Expr
generateCall mode func args =
  case func of
    Opt.VarGlobal global@(Opt.Global (ModuleName.Canonical pkg _) _) | pkg == Pkg.core ->
      generateCoreCall mode global args

    Opt.VarBox _ ->
      case mode of
        Mode.Dev _ _ ->
          generateCallHelp mode func args

        Mode.Prod _ _ ->
          case args of
            [arg] ->
              generateLamExpr mode arg

            _ ->
              generateCallHelp mode func args

    _ ->
      generateCallHelp mode func args


generateCallHelp :: Mode.Mode -> Opt.Expr -> [Opt.Expr] -> L.Expr
generateCallHelp mode func args =
  generateNormalCall
    (generateLamExpr mode func)
    (map (generateLamExpr mode) args)


generateGlobalCall :: ModuleName.Canonical -> N.Name -> [L.Expr] -> L.Expr
generateGlobalCall home name args =
  generateNormalCall (L.Ref (Name.fromGlobal home name)) args


generateNormalCall :: L.Expr -> [L.Expr] -> L.Expr
generateNormalCall func args =
  case IntMap.lookup (length args) callHelpers of
    Just helper ->
      L.Call helper (func:args)

    Nothing ->
      List.foldl' (\f a -> L.Call f [a]) func args


{-# NOINLINE callHelpers #-}
callHelpers :: IntMap.IntMap L.Expr
callHelpers =
  IntMap.fromList $
    map (\n -> (n, L.Ref (Name.makeA n))) [2..9]



-- CORE CALLS


generateCoreCall :: Mode.Mode -> Opt.Global -> [Opt.Expr] -> L.Expr
generateCoreCall mode (Opt.Global home@(ModuleName.Canonical _ moduleName) name) args =
  if moduleName == N.basics then
    generateBasicsCall mode home name args

  else if moduleName == N.bitwise then
    generateBitwiseCall home name (map (generateLamExpr mode) args)

  else if moduleName == N.tuple then
    generateTupleCall home name (map (generateLamExpr mode) args)

  else if moduleName == N.jsArray then
    generateLamArrayCall home name (map (generateLamExpr mode) args)

  else
    generateGlobalCall home name (map (generateLamExpr mode) args)


generateTupleCall :: ModuleName.Canonical -> N.Name -> [L.Expr] -> L.Expr
generateTupleCall home name args =
  case args of
    [value] ->
      case name of
        "first"  -> L.Access value (Name.fromLocal "a")
        "second" -> L.Access value (Name.fromLocal "b")
        _        -> generateGlobalCall home name args

    _ ->
      generateGlobalCall home name args


generateLamArrayCall :: ModuleName.Canonical -> N.Name -> [L.Expr] -> L.Expr
generateLamArrayCall home name args =
  case args of
    [entry]        | name == "singleton" -> L.Array [entry]
    [index, array] | name == "unsafeGet" -> L.Index array index
    _                                    -> generateGlobalCall home name args


generateBitwiseCall :: ModuleName.Canonical -> N.Name -> [L.Expr] -> L.Expr
generateBitwiseCall home name args =
  case args of
    [arg] ->
      case name of
        "complement" -> L.Prefix L.PrefixBNot arg
        _            -> generateGlobalCall home name args

    [left,right] ->
      case name of
        "and"            -> L.Infix L.OpBAnd     left right
        "or"             -> L.Infix L.OpBOr      left right
        "xor"            -> L.Infix L.OpBXor     left right
        "shiftLeftBy"    -> L.Infix L.OpLShift   right left
        "shiftRightBy"   -> L.Infix L.OpSpRShift right left
        "shiftRightZfBy" -> L.Infix L.OpZfRShift right left
        _                -> generateGlobalCall home name args

    _ ->
      generateGlobalCall home name args


generateBasicsCall :: Mode.Mode -> ModuleName.Canonical -> N.Name -> [Opt.Expr] -> L.Expr
generateBasicsCall mode home name args =
  case args of
    [elmArg] ->
      let arg = generateLamExpr mode elmArg in
      case name of
        "not"      -> L.Prefix L.PrefixLNot arg
        "negate"   -> L.Prefix L.PrefixMinus arg
        "toFloat"  -> arg
        "truncate" -> L.Infix L.OpBOr arg (L.Int 0)
        _          -> generateGlobalCall home name [arg]

    [elmLeft, elmRight] ->
      case name of
        "composeL" -> decomposeL mode elmLeft [elmRight]
        "composeR" -> decomposeR mode [elmLeft] elmRight
        "append"   -> append mode elmLeft elmRight
        "apL"      -> generateLamExpr mode $ apply elmLeft elmRight
        "apR"      -> generateLamExpr mode $ apply elmRight elmLeft
        _ ->
          let
            left = generateLamExpr mode elmLeft
            right = generateLamExpr mode elmRight
          in
          case name of
            "add"  -> L.Infix L.OpAdd left right
            "sub"  -> L.Infix L.OpSub left right
            "mul"  -> L.Infix L.OpMul left right
            "fdiv" -> L.Infix L.OpDiv left right
            "idiv" -> L.Infix L.OpBOr (L.Infix L.OpDiv left right) (L.Int 0)
            "eq"   -> equal left right
            "neq"  -> notEqual left right
            "lt"   -> cmp L.OpLT  L.OpLT   0  left right
            "gt"   -> cmp L.OpGT  L.OpGT   0  left right
            "le"   -> cmp L.OpLEq L.OpLT   1  left right
            "ge"   -> cmp L.OpGEq L.OpGT (-1) left right
            "or"   -> L.Infix L.OpLOr         left right
            "and"  -> L.Infix L.OpLAnd        left right
            "xor"  -> L.Infix L.OpStrictNEq   left right
            "remainderBy" -> L.Infix L.OpMod right left
            _      -> generateGlobalCall home name [left, right]

    _ ->
      generateGlobalCall home name (map (generateLamExpr mode) args)


equal :: L.Expr -> L.Expr -> L.Expr
equal left right =
  if isLiteral left || isLiteral right then
    strictEq left right
  else
    L.Call (L.Ref (Name.fromKernel N.utils "eq")) [left, right]


notEqual :: L.Expr -> L.Expr -> L.Expr
notEqual left right =
  if isLiteral left || isLiteral right then
    strictNEq left right
  else
    L.Prefix L.PrefixLNot $
      L.Call (L.Ref (Name.fromKernel N.utils "eq")) [left, right]


cmp :: L.InfixOp -> L.InfixOp -> Int -> L.Expr -> L.Expr -> L.Expr
cmp idealOp backupOp backupInt left right =
  if isLiteral left || isLiteral right then
    L.Infix idealOp left right
  else
    L.Infix backupOp
      (L.Call (L.Ref (Name.fromKernel N.utils "cmp")) [left, right])
      (L.Int backupInt)


isLiteral :: L.Expr -> Bool
isLiteral expr =
  case expr of
    L.String _ ->
      True

    L.Float _ ->
      True

    L.Int _ ->
      True

    L.Bool _ ->
      True

    _ ->
      False


decomposeL :: Mode.Mode -> Opt.Expr -> [Opt.Expr] -> L.Expr
decomposeL mode expr funcs =
  case expr of
    Opt.Call (Opt.VarGlobal (Opt.Global home "composeL")) [left, func]
      | home == ModuleName.basics ->
          decomposeL mode left (func:funcs)

    _ ->
      generateLamExpr mode $
        Opt.Function [N.dollar] (foldr apply (Opt.VarLocal N.dollar) (expr:funcs))


decomposeR :: Mode.Mode -> [Opt.Expr] -> Opt.Expr -> L.Expr
decomposeR mode funcs expr =
  case expr of
    Opt.Call (Opt.VarGlobal (Opt.Global home "composeR")) [func, right]
      | home == ModuleName.basics ->
          decomposeR mode (func:funcs) right

    _ ->
      generateLamExpr mode $
        Opt.Function [N.dollar] (foldr apply (Opt.VarLocal N.dollar) (expr:funcs))


apply :: Opt.Expr -> Opt.Expr -> Opt.Expr
apply func value =
  case func of
    Opt.Accessor field ->
      Opt.Access value field

    Opt.Call f args ->
      Opt.Call f (args ++ [value])

    _ ->
      Opt.Call func [value]


append :: Mode.Mode -> Opt.Expr -> Opt.Expr -> L.Expr
append mode left right =
  let seqs = generateLamExpr mode left : toSeqs mode right in
  if any isStringLiteral seqs then
    foldr1 (L.Infix L.OpAdd) seqs
  else
    foldr1 jsAppend seqs


jsAppend :: L.Expr -> L.Expr -> L.Expr
jsAppend a b =
  L.Call (L.Ref (Name.fromKernel N.utils "ap")) [a, b]


toSeqs :: Mode.Mode -> Opt.Expr -> [L.Expr]
toSeqs mode expr =
  case expr of
    Opt.Call (Opt.VarGlobal (Opt.Global home "append")) [left, right]
      | home == ModuleName.basics ->
          generateLamExpr mode left : toSeqs mode right

    _ ->
      [generateLamExpr mode expr]


isStringLiteral :: L.Expr -> Bool
isStringLiteral expr =
  case expr of
    L.String _ ->
      True

    _ ->
      False



-- SIMPLIFY INFIX OPERATORS


strictEq :: L.Expr -> L.Expr -> L.Expr
strictEq left right =
  case left of
    L.Int 0 ->
      L.Prefix L.PrefixLNot right

    L.Bool bool ->
      if bool then right else L.Prefix L.PrefixLNot right

    _ ->
      case right of
        L.Int 0 ->
          L.Prefix L.PrefixLNot left

        L.Bool bool ->
          if bool then left else L.Prefix L.PrefixLNot left

        _ ->
          L.Infix L.OpStrictEq left right


strictNEq :: L.Expr -> L.Expr -> L.Expr
strictNEq left right =
  case left of
    L.Int 0 ->
      right

    L.Bool bool ->
      if bool then L.Prefix L.PrefixLNot right else right

    _ ->
      case right of
        L.Int 0 ->
          left

        L.Bool bool ->
          if bool then L.Prefix L.PrefixLNot left else left

        _ ->
          L.Infix L.OpStrictNEq left right



-- TAIL CALL


-- TODO check if L minifiers collapse unnecessary temporary variables
--
generateTailCall :: Mode.Mode -> N.Name -> [(N.Name, Opt.Expr)] -> [L.Stmt]
generateTailCall mode name args =
  let
    toTempVars (argName, arg) =
      ( Name.makeTemp argName, Just (generateLamExpr mode arg) )

    toRealVars (argName, _) =
      L.ExprStmt $
        L.Assign (L.LRef (Name.fromLocal argName)) (L.Ref (Name.makeTemp argName))
  in
  L.Var (map toTempVars args)
  : map toRealVars args
  ++ [ L.Continue (Just (Name.fromLocal name)) ]



-- DEFINITIONS


generateDef :: Mode.Mode -> Opt.Def -> L.Stmt
generateDef mode def =
  case def of
    Opt.Def name body ->
      L.Var [ (Name.fromLocal name, Just (generateLamExpr mode body)) ]

    Opt.TailDef name argNames body ->
      L.Var [ (Name.fromLocal name, Just (codeToExpr (generateTailDef mode name argNames body))) ]


generateTailDef :: Mode.Mode -> N.Name -> [N.Name] -> Opt.Expr -> Code
generateTailDef mode name argNames body =
  generateFunction (map Name.fromLocal argNames) $ LamBlock $
    [ L.Labelled (Name.fromLocal name) $
        L.While (L.Bool True) $
          codeToStmt $ generate mode body
    ]



-- PATHS


generatePath :: Mode.Mode -> Opt.Path -> L.Expr
generatePath mode path =
  case path of
    Opt.Index index subPath ->
      L.Access (generatePath mode subPath) (Name.fromIndex index)

    Opt.Root name ->
      L.Ref (Name.fromLocal name)

    Opt.Field field subPath ->
      L.Access (generatePath mode subPath) (generateField mode field)

    Opt.Unbox subPath ->
      case mode of
        Mode.Dev _ _ ->
          L.Access (generatePath mode subPath) (Name.fromIndex Index.first)

        Mode.Prod _ _ ->
          generatePath mode subPath



-- GENERATE IFS


generateIf :: Mode.Mode -> [(Opt.Expr, Opt.Expr)] -> Opt.Expr -> Code
generateIf mode givenBranches givenFinal =
  let
    (branches, final) =
      crushIfs givenBranches givenFinal

    convertBranch (condition, expr) =
      ( generateLamExpr mode condition
      , generate mode expr
      )

    branchExprs = map convertBranch branches
    finalCode = generate mode final
  in
  if isBlock finalCode || any (isBlock . snd) branchExprs then
    LamBlock [ foldr addStmtIf (codeToStmt finalCode) branchExprs ]
  else
    LamExpr $ foldr addExprIf (codeToExpr finalCode) branchExprs


addExprIf :: (L.Expr, Code) -> L.Expr -> L.Expr
addExprIf (condition, branch) final =
  L.If condition (codeToExpr branch) final


addStmtIf :: (L.Expr, Code) -> L.Stmt -> L.Stmt
addStmtIf (condition, branch) final =
  L.IfStmt condition (codeToStmt branch) final


isBlock :: Code -> Bool
isBlock code =
  case code of
    LamBlock _ -> True
    LamExpr _ -> False


crushIfs :: [(Opt.Expr, Opt.Expr)] -> Opt.Expr -> ([(Opt.Expr, Opt.Expr)], Opt.Expr)
crushIfs branches final =
  crushIfsHelp [] branches final


crushIfsHelp
    :: [(Opt.Expr, Opt.Expr)]
    -> [(Opt.Expr, Opt.Expr)]
    -> Opt.Expr
    -> ([(Opt.Expr, Opt.Expr)], Opt.Expr)
crushIfsHelp visitedBranches unvisitedBranches final =
  case unvisitedBranches of
    [] ->
        case final of
          Opt.If subBranches subFinal ->
              crushIfsHelp visitedBranches subBranches subFinal

          _ ->
              (reverse visitedBranches, final)

    visiting : unvisited ->
        crushIfsHelp (visiting : visitedBranches) unvisited final



-- CASE EXPRESSIONS


generateCase :: Mode.Mode -> N.Name -> N.Name -> Opt.Decider Opt.Choice -> [(Int, Opt.Expr)] -> [L.Stmt]
generateCase mode label root decider jumps =
  foldr (goto mode label) (generateDecider mode label root decider) jumps


goto :: Mode.Mode -> N.Name -> (Int, Opt.Expr) -> [L.Stmt] -> [L.Stmt]
goto mode label (index, branch) stmts =
  let
    labeledDeciderStmt =
      L.Labelled
        (Name.makeLabel label index)
        (L.While (L.Bool True) (L.Block stmts))
  in
  labeledDeciderStmt : codeToStmtList (generate mode branch)


generateDecider :: Mode.Mode -> N.Name -> N.Name -> Opt.Decider Opt.Choice -> [L.Stmt]
generateDecider mode label root decisionTree =
  case decisionTree of
    Opt.Leaf (Opt.Inline branch) ->
      codeToStmtList (generate mode branch)

    Opt.Leaf (Opt.Jump index) ->
      [ L.Break (Just (Name.makeLabel label index)) ]

    Opt.Chain testChain success failure ->
      [ L.IfStmt
          (List.foldl1' (L.Infix L.OpLAnd) (map (generateIfTest mode root) testChain))
          (L.Block $ generateDecider mode label root success)
          (L.Block $ generateDecider mode label root failure)
      ]

    Opt.FanOut path edges fallback ->
      [ L.Switch
          (generateCaseTest mode root path (fst (head edges)))
          ( foldr
              (\edge cases -> generateCaseBranch mode label root edge : cases)
              [ L.Default (generateDecider mode label root fallback) ]
              edges
          )
      ]


generateIfTest :: Mode.Mode -> N.Name -> (DT.Path, DT.Test) -> L.Expr
generateIfTest mode root (path, test) =
  let
    value = pathToLamExpr mode root path
  in
  case test of
    DT.IsCtor home name index _ opts ->
      let
        tag =
          case mode of
            Mode.Dev _ _ -> L.Access value Name.dollar
            Mode.Prod _ _ ->
              case opts of
                Can.Normal -> L.Access value Name.dollar
                Can.Enum   -> value
                Can.Unbox  -> value
      in
      strictEq tag $
        case mode of
          Mode.Dev _ _ -> L.String (N.toBuilder name)
          Mode.Prod _ _ -> L.Int (ctorToInt home name index)

    DT.IsBool True ->
      value

    DT.IsBool False ->
      L.Prefix L.PrefixLNot value

    DT.IsInt int ->
      strictEq value (L.Int int)

    DT.IsChr char ->
      strictEq (L.String (Text.encodeUtf8Builder char)) $
        case mode of
          Mode.Dev _ _ -> L.Call (L.Access value (Name.fromLocal "valueOf")) []
          Mode.Prod _ _ -> value

    DT.IsStr string ->
      strictEq value (L.String (Text.encodeUtf8Builder string))

    DT.IsCons ->
      L.Access value (Name.fromLocal "b")

    DT.IsNil ->
      L.Prefix L.PrefixLNot $
        L.Access value (Name.fromLocal "b")

    DT.IsTuple ->
      error "COMPILER BUG - there should never be tests on a tuple"



generateCaseBranch :: Mode.Mode -> N.Name -> N.Name -> (DT.Test, Opt.Decider Opt.Choice) -> L.Case
generateCaseBranch mode label root (test, subTree) =
  L.Case
    (generateCaseValue mode test)
    (generateDecider mode label root subTree)


generateCaseValue :: Mode.Mode -> DT.Test -> L.Expr
generateCaseValue mode test =
  case test of
    DT.IsCtor home name index _ _ ->
      case mode of
        Mode.Dev _ _ -> L.String (N.toBuilder name)
        Mode.Prod _ _ -> L.Int (ctorToInt home name index)

    DT.IsInt int ->
      L.Int int

    DT.IsChr char ->
      L.String (Text.encodeUtf8Builder char)

    DT.IsStr string ->
      L.String (Text.encodeUtf8Builder string)

    DT.IsBool _ ->
      error "COMPILER BUG - there should never be three tests on a boolean"

    DT.IsCons ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsNil ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsTuple ->
      error "COMPILER BUG - there should never be three tests on a tuple"


generateCaseTest :: Mode.Mode -> N.Name -> DT.Path -> DT.Test -> L.Expr
generateCaseTest mode root path exampleTest =
  let
    value = pathToLamExpr mode root path
  in
  case exampleTest of
    DT.IsCtor home name _ _ opts ->
      if name == N.bool && home == ModuleName.basics then
        value
      else
        case mode of
          Mode.Dev _ _ ->
            L.Access value Name.dollar

          Mode.Prod _ _ ->
            case opts of
              Can.Normal ->
                L.Access value Name.dollar

              Can.Enum ->
                value

              Can.Unbox ->
                value

    DT.IsInt _ ->
      value

    DT.IsStr _ ->
      value

    DT.IsChr _ ->
      case mode of
        Mode.Dev _ _ ->
          L.Call (L.Access value (Name.fromLocal "valueOf")) []

        Mode.Prod _ _ ->
          value

    DT.IsBool _ ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsCons ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsNil ->
      error "COMPILER BUG - there should never be three tests on a list"

    DT.IsTuple ->
      error "COMPILER BUG - there should never be three tests on a list"



-- PATTERN PATHS


pathToLamExpr :: Mode.Mode -> N.Name -> DT.Path -> L.Expr
pathToLamExpr mode root path =
  case path of
    DT.Index index subPath ->
      L.Access (pathToLamExpr mode root subPath) (Name.fromIndex index)

    DT.Unbox subPath ->
      case mode of
        Mode.Dev _ _ ->
          L.Access (pathToLamExpr mode root subPath) (Name.fromIndex Index.first)

        Mode.Prod _ _ ->
          pathToLamExpr mode root subPath

    DT.Empty ->
      L.Ref (Name.fromLocal root)



-- GENERATE MAIN


generateMain :: Mode.Mode -> ModuleName.Canonical -> Opt.Main -> L.Expr
generateMain mode home main =
  case main of
    Opt.Static ->
      L.Ref (Name.fromKernel N.virtualDom "init")
        # L.Ref (Name.fromGlobal home "main")
        # L.Int 0
        # L.Int 0

    Opt.Dynamic msgType decoder ->
      L.Ref (Name.fromGlobal home "main")
        # generateLamExpr mode decoder
        # toDebugMetadata mode msgType


(#) :: L.Expr -> L.Expr -> L.Expr
(#) func arg =
  L.Call func [arg]


toDebugMetadata :: Mode.Mode -> Can.Type -> L.Expr
toDebugMetadata mode msgType =
  case mode of
    Mode.Prod _ _ ->
      L.Int 0

    Mode.Dev _ Nothing ->
      L.Int 0

    Mode.Dev _ (Just interfaces) ->
      L.Lamon $ Encode.object $
        [ ("versions", Encode.object [ ("elm", Pkg.encodeVersion Version.version) ])
        , ("types", Type.encodeMetadata (Extract.fromMsg interfaces msgType))
        ]
