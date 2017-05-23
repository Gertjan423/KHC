
module Frontend.HsParser (hsParse) where

-- | Main types
import Frontend.HsTypes
import Utils.Kind (Kind(..))
import Utils.Var (Sym, mkSym, PsTyVar, mkPsTyVar, PsTmVar, mkPsTmVar)
import Utils.Annotated (Ann((:|)))

-- | Utilities
import Data.Functor (($>))
import Control.Applicative

-- Lexer
import qualified Text.Parsec.Token as T

-- Parser
import Text.Parsec.Char (lower, upper, oneOf, alphaNum)
import Text.Parsec.Combinator (chainl1, chainr1, sepBy1, eof)
import Text.Parsec.Prim (Parsec, (<?>), try, parse)

-- * The Parsing Monad
-- ------------------------------------------------------------------------------

type PsM a = Parsec String () a

-- | Parse a complete program from a file
hsParse :: FilePath -> IO (Either String PsProgram)
hsParse path = readFile path >>= \contents ->
  return $ case parse parser path contents of
             Left err -> Left (show err)
             Right p  -> Right p
  where
    parser = whiteSpace *> pProgram <* eof

-- * The Lexer and Utilities
-- ------------------------------------------------------------------------------

-- | Haskell subset we use
haskellDef :: T.LanguageDef st
haskellDef = T.LanguageDef
               { T.commentStart    = "{-"
               , T.commentEnd      = "-}"
               , T.commentLine     = "--"
               , T.nestedComments  = True
               , T.identStart      = lower -- letter
               , T.identLetter     = alphaNum <|> oneOf "_'"
               , T.opStart         = T.opLetter haskellDef
               , T.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
               , T.reservedOpNames = [ "::","=","\\","|","->","@","=>" ]
               , T.reservedNames   = [ "let","in","case","of", "data"
                                     , "class", "instance", "where", "forall" ]
               , T.caseSensitive   = True
               }

-- | The lexer
lexer :: T.TokenParser st
lexer = T.makeTokenParser haskellDef

-- | Parse an identifier that starts with a lowercase
lowerIdent :: PsM Sym
lowerIdent = mkSym <$> T.identifier lexer

-- | Parse an identifier that starts with an uppercase
upperIdent :: PsM Sym
upperIdent = lexeme $ do
  c  <- upper
  cs <- many (alphaNum <|> oneOf "_'")
  return (mkSym (c:cs))

-- | Turn a parser into a lexeme parser
lexeme :: PsM a -> PsM a
lexeme = T.lexeme lexer

-- | Parse a reserved keyword
reserved :: String -> PsM ()
reserved = T.reserved lexer

-- | Parse a reserved operator
reservedOp :: String -> PsM ()
reservedOp = T.reservedOp lexer

-- | Parse a specific string
symbol :: String -> PsM ()
symbol s = T.symbol lexer s *> return ()

-- | Parse zero or more whitespace
whiteSpace :: PsM () -- Use at the start of the file
whiteSpace = T.whiteSpace lexer

-- | Parse something enclosed in parentheses
parens :: PsM a -> PsM a
parens = T.parens lexer

-- | Parse something enclosed in brackets
braces :: PsM a -> PsM a
braces = T.braces lexer

-- | Parse a dot
dot :: PsM ()
dot = T.dot lexer $> ()

-- | Parse a semicolon-separated list of things
semiSep :: PsM a -> PsM [a]
semiSep = T.semiSep lexer

-- | Parse a comma-separated list of things
commaSep :: PsM a -> PsM [a]
commaSep = T.commaSep lexer

-- | The Monoidal applicative operator
infixl 5 <&>
(<&>) :: Applicative f => f a -> f b -> f (a, b)
(<&>) = liftA2 (,)

-- * Parse Declarations and Programs
-- ------------------------------------------------------------------------------

-- | Parse a program
pProgram :: PsM PsProgram
pProgram  =  PgmCls  <$> pClsDecl  <*> pProgram
         <|> PgmInst <$> pInstDecl <*> pProgram
         <|> PgmData <$> pDataDecl <*> pProgram
         <|> PgmExp  <$> pTerm

-- | Parse a class declaration
pClsDecl :: PsM PsClsDecl
pClsDecl  =  (\ctx cls a (m,ty) -> ClsD ctx cls a m ty)
         <$  reserved "class"
         <*> pCts
         <*  reservedOp "=>"
         <*> pClass
         <*> parens pTyVarWithKind
         <*  reserved "where"
         <*> braces (pTmVar <&> (reservedOp "::" *> pPolyTy))

-- | Parse an instance declaration
pInstDecl :: PsM PsInsDecl
pInstDecl  =  (\ctx cls ty (m,tm) -> InsD ctx cls ty m tm)
          <$  reserved "instance"
          <*> pCts
          <*  reservedOp "=>"
          <*> pClass
          <*> pPrimTyPat
          <*  reserved "where"
          <*> braces (pTmVar <&> (reservedOp "=" *> pTerm))

-- | Parse a datatype declaration
pDataDecl :: PsM PsDataDecl
pDataDecl  =  DataD
          <$  reserved "data"
          <*> pTyCon
          <*> many (parens pTyVarWithKind)
          <*  reservedOp "="
          <*> sepBy1 (pDataCon <&> many pPrimTy) (reservedOp "|")


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
pPolyTy  =  PPoly <$  reserved "forall" <*> parens pTyVarWithKind <* dot <*> pPolyTy
        <|> PQual <$> pQualTy

-- | Parse a qualified type
pQualTy :: PsM PsQualTy
pQualTy  =  try (QQual <$> pPrimCtr <* reservedOp "=>" <*> pQualTy)
        <|> QMono <$> pMonoTy

-- | Parse a primitive monotype
pPrimTy :: PsM PsMonoTy
pPrimTy = parens pMonoTy <|> TyCon <$> pTyCon <|> TyVar <$> pTyVar

-- | Parse a monotype
pMonoTy :: PsM PsMonoTy
pMonoTy = chainr1 (chainl1 pPrimTy (pure TyApp))
                  (mkPsArrowTy <$ reservedOp "->")

-- | Parse a primitive type pattern
pPrimTyPat :: PsM PsTyPat
pPrimTyPat  =  HsTyConPat <$> pTyCon
           <|> parens (try pTyPat <|> HsTyVarPat <$> pTyVarWithKind)

-- | Parse a type pattern
pTyPat :: PsM PsTyPat
pTyPat = chainl1 pPrimTyPat (pure HsTyAppPat)

-- | Parse a kind
pKind :: PsM Kind
pKind  =  chainr1 (parens pKind <|> (KStar <$ symbol "*")) (KArr <$ reservedOp "->")
      <?> "a kind"

-- | Parse a primitive constraint
pPrimCtr :: PsM PsCtr
pPrimCtr = parens pCtr <|> pClassCtr

-- | Parse a constraint
pImplCtr :: PsM PsCtr
pImplCtr = chainr1 pPrimCtr (CtrImpl <$ reservedOp "=>")

-- | Parse a forall constraint
pCtr :: PsM PsCtr
pCtr  =  CtrAbs
         <$  reserved "forall"
         <*> parens pTyVarWithKind
         <*  dot
         <*> pCtr
     <|> pImplCtr

-- | Parse a class constraint
pClassCtr :: PsM PsCtr
pClassCtr = fmap CtrClsCt (ClsCt <$> pClass <*> pPrimTy)

-- | Parse a class/instance context
pCts :: PsM PsCts
pCts = parens (commaSep pCtr)

-- | Parse a kind-annotated type variable (without the parentheses!!)
pTyVarWithKind :: PsM PsTyVarWithKind
pTyVarWithKind = liftA2 (:|) pTyVar (reservedOp "::" *> pKind)

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
          <$  reservedOp "\\"
          <*> pTmVar
          <*  dot
          <*> pTerm
      <|> uncurry TmLet
          <$  reserved "let"
          <*> braces (pTmVar <&> (reservedOp "=" *> pTerm))
          <*  reserved "in"
          <*> pTerm
      <|> TmCase
          <$  reserved "case"
          <*> pTerm
          <*  reserved "of"
          <*> braces (semiSep pAlt)

-- | Parse a pattern
pPat :: PsM PsPat
pPat = HsPat <$> pDataCon <*> many pTmVar

-- | Parse a case alternative
pAlt :: PsM PsAlt
pAlt = HsAlt <$> pPat <* reservedOp "->" <*> pTerm

