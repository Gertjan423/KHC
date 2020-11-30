
module Frontend.HsParser (hsParse) where

-- | Main types
import Frontend.HsTypes
import Utils.Kind (Kind(..))
import Utils.Var (Sym, mkSym, PsTyVar, mkPsTyVar, PsTmVar, mkPsTmVar)
import Utils.Annotated (Ann((:|)))

-- | Utilities
import Control.Applicative (Alternative, liftA2, (<**>))
import Data.Functor (($>))
import Data.Void (Void)
import Control.Monad.Reader

-- Lexer
import qualified Text.Megaparsec.Char.Lexer as L

-- Parser
import Text.Megaparsec
import Text.Megaparsec.Char

-- * The Parsing Monad
-- ------------------------------------------------------------------------------

type PsM = ReaderT SpaceConsumer (Parsec Void String)
newtype SpaceConsumer = SC (PsM ())

-- | Parse a complete program from a file
hsParse :: FilePath -> IO (Either String PsProgram)
hsParse path = readFile path >>= \contents ->
  return $ case parse (runReaderT parser (SC sc)) path contents of
    Left err -> Left (errorBundlePretty err)
    Right p  -> Right p
  where
    parser = sc *> pProgram <* eof

-- * The Lexer and Utilities
-- ------------------------------------------------------------------------------

-- | The space comsumer
sc :: PsM ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{--" "--}")

-- | Turn a parser indent aware
indent :: PsM a -> PsM a
indent p =
  ask >>= \(SC sc') ->
    L.lineFold sc' $ \sc'' ->
      local (const (SC (try sc'' <|> return ()))) (p <* sc')

-- | Turn a parser into a lexeme parser
lexeme :: PsM a -> PsM a
lexeme x = ask >>= \(SC sc') -> L.lexeme sc' x

-- | List of reserved names
reservedNames :: [String]
reservedNames =
  ["let", "in", "case", "of", "data", "class", "instance", "where", "forall"]

-- | Parse an identifier given a parser for the first character
identifier :: PsM Char -> PsM Sym
identifier firstChar = mkSym <$> (lexeme . try) (p >>= check)
  where
    p = (:) <$> firstChar <*> many (alphaNumChar <|> oneOf "_'")
    check x =
      if x `elem` reservedNames
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

-- | Parse an identifier that starts with a lowercase
lowerIdent :: PsM Sym
lowerIdent = identifier lowerChar

-- | Parse an identifier that starts with an uppercase
upperIdent :: PsM Sym
upperIdent = identifier upperChar

-- | Parse a specific string
symbol :: String -> PsM ()
symbol s = ask >>= \(SC sc') -> L.symbol sc' s $> ()

-- | Parse something enclosed in parentheses
parens :: PsM a -> PsM a
parens = between (symbol "(") (symbol ")")

-- | Parse a dot
dot :: PsM ()
dot = symbol "."

-- | Parse a comma-separated list of things
commaSep :: PsM a -> PsM [a]
commaSep = (`sepBy` symbol ",")

-- | The Monoidal applicative operator
infixl 5 <&>
(<&>) :: Applicative f => f a -> f b -> f (a, b)
(<&>) = liftA2 (,)

-- | Left associative operator chaining
chainl1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan where
  scan = p <**> rst
  rst = (\f y g x -> g (f x y)) <$> op <*> p <*> rst <|> pure id

-- | Right associative operator chaining
chainr1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainr1 p op = scan where
  scan = p <**> rst
  rst = (flip <$> op <*> scan) <|> pure id

-- * Parse Declarations and Programs
-- ------------------------------------------------------------------------------

-- | Parse a program
pProgram :: PsM PsProgram
pProgram  =  PgmCls  <$> pClsDecl  <*> pProgram
         <|> PgmInst <$> pInstDecl <*> pProgram
         <|> PgmData <$> pDataDecl <*> pProgram
         <|> PgmFunc <$> pFuncDecl <*> pProgram
         <|> PgmExp  <$> pTerm

-- | Parse a class declaration
pClsDecl :: PsM PsClsDecl
pClsDecl  =  indent $ (\ctx cls a (m,ty) -> ClsD ctx cls a m ty)
         <$  symbol "class"
         <*> pClassCts
         <*> pClass
         <*> pTyVarWithKind
         <*  symbol "where"
         <*> (pTmVar <&> (symbol "::" *> pPolyTy))

-- | Parse an instance declaration
pInstDecl :: PsM PsInsDecl
pInstDecl  =  indent $ (\ctx cls ty (m,tm) -> InsD ctx cls ty m tm)
          <$  symbol "instance"
          <*> pClassCts
          <*> pClass
          <*> pPrimTyPat
          <*  symbol "where"
          <*> (pTmVar <&> (symbol "=" *> pTerm))

-- | Parse a datatype declaration
pDataDecl :: PsM PsDataDecl
pDataDecl  =  indent $ DataD
          <$  symbol "data"
          <*> pTyCon
          <*> many (parens pTyVarWithKind)
          <*  symbol "="
          <*> sepBy1 (pDataCon <&> many pPrimTy) (symbol "|")

-- | Parse a function declaration
pFuncDecl :: PsM PsFuncDecl
pFuncDecl  =  indent $ FuncD
          <$> pTmVar
          <*  symbol "::"
          <*> pPolyTy
          <*  symbol "="
          <*> pTerm

-- * Parse all kinds of names
-- ------------------------------------------------------------------------------

-- | Parse a type variable
pTyVar :: PsM PsTyVar
pTyVar = mkPsTyVar <$> lowerIdent <?> "a type variable"

-- | Parse a term variable
pTmVar :: PsM PsTmVar
pTmVar = mkPsTmVar <$> lowerIdent <?> "a term variable"

-- | Parse a class name
pClass :: PsM PsClass
pClass = Class <$> upperIdent <?> "a class name"

-- | Parse a type constructor
pTyCon :: PsM PsTyCon
pTyCon = HsTC <$> upperIdent <?> "a type constructor"

-- | Parse a data constructor
pDataCon :: PsM PsDataCon
pDataCon = HsDC <$> upperIdent <?> "a data constructor"

-- * Parse types, type patterns, kinds and constraints
-- ------------------------------------------------------------------------------

-- | Parse a polytype
pPolyTy :: PsM PsPolyTy
pPolyTy =
  PPoly <$ symbol "forall" <*> parens pTyVarWithKind <* dot <*> pPolyTy <|>
  PQual <$> pQualTy

-- | Parse a qualified type -- Type Well-formedness says 1 constraint
pQualTy :: PsM PsQualTy
pQualTy =
  try (QQual <$> pClassCtr <* symbol "=>" <*> pQualTy) <|> QMono <$> pMonoTy

-- | Parse a primitive monotype
pPrimTy :: PsM PsMonoTy
pPrimTy = parens pMonoTy <|> TyCon <$> pTyCon <|> TyVar <$> pTyVar

-- | Parse a type pattern
pPrimTyPat :: PsM PsTyPat
pPrimTyPat = parens pMonoTyPat <|> HsTyConPat <$> pTyCon <|> HsTyVarPat <$> pTyVarWithKind

-- | Parse a monotype
pMonoTy :: PsM PsMonoTy
pMonoTy = chainr1 (chainl1 pPrimTy (pure TyApp))
                  (mkPsArrowTy <$ symbol "->")

-- | Parse a monotype pattern
pMonoTyPat :: PsM PsTyPat
pMonoTyPat = chainr1 (chainl1 pPrimTyPat (pure HsTyAppPat))
                  (mkPsArrowTyPat <$ symbol "->")

-- | Parse a kind
pKind :: PsM Kind
pKind = chainr1 (parens pKind <|> (KStar <$ symbol "*")) (KArr <$ symbol "->")
     <?> "a kind"

-- | Parse a class constraint
pClassCtr :: PsM PsClsCt
pClassCtr = ClsCt <$> pClass <*> pPrimTy

-- | Parse a class/instance context
pClassCts :: PsM PsClsCs
pClassCts  =  option [] . try
           $  (parens (commaSep pClassCtr)
          <|> (pure <$> pClassCtr))
          <*  symbol "=>"

-- | Parse a kind-annotated type variable (without the parentheses!!)
pTyVarWithKind :: PsM PsTyVarWithKind
pTyVarWithKind = liftA2 (:|) pTyVar (symbol "::" *> pKind)

-- * Parse terms
-- ------------------------------------------------------------------------------

-- | Parse a term (highest priority)
pPrimTerm :: PsM PsTerm
pPrimTerm  =  TmVar <$> pTmVar
          <|> TmCon <$> pDataCon
          <|> parens pTerm

-- | Parse a term (medium priority)
pAppTerm :: PsM PsTerm
pAppTerm = chainl1 pPrimTerm (pure TmApp)

-- | Parse a term (lowest priority)
pTerm :: PsM PsTerm
pTerm  =  pAppTerm
      <|> TmAbs
          <$  symbol "\\"
          <*> pTmVar
          <*  dot
          <*> pTerm
      <|> uncurry TmLet
          <$  symbol "let"
          <*> (pTmVar <&> (symbol "=" *> pTerm))
          <*  symbol "in"
          <*> pTerm
      <|> TmCase
          <$  symbol "case"
          <*> pTerm
          <*  symbol "of"
          <*> some (indent pAlt)

-- | Parse a pattern
pPat :: PsM PsPat
pPat = HsPat <$> pDataCon <*> many pTmVar

-- | Parse a case alternative
pAlt :: PsM PsAlt
pAlt = HsAlt <$> pPat <* symbol "->" <*> pTerm
