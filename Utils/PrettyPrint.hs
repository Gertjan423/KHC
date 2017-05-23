
module Utils.PrettyPrint
( -- All combinators I liked from PrettyPrint.HughesPJ
  (<>), (<+>), ($$), ($+$)
, hcat, hsep, vcat, sep, cat, fsep, fcat
, parens, brackets, braces, quotes, doubleQuotes
, maybeParens, maybeBrackets, maybeBraces, maybeQuotes, maybeDoubleQuotes
, nest, hang, punctuate
, text, int, integer, rational, double, float, char
, empty, blankLine, semi, comma, colon, space, equals
, lparen, rparen, lbrack, rbrack, lbrace, rbrace
, underscore, dcolon, arrow, darrow, dot, backslash

  -- Render a document
, render, renderError, renderWithColor

  -- Rendering modes
, PMode, colorMode, plainMode, renderWithMode

  -- Colors
, Color, colorDoc, boldColorDoc
, red, green, yellow, blue, purple, turquoise, white, gray

  -- The abstract Doc type and the main class
, Doc, PrettyPrint(..), pprPar
) where

import Data.Maybe (isJust)
import qualified Text.PrettyPrint.HughesPJ as P

-- | The Doc type is just a wrapper for the Doc from Hughes and SPJ
-- ----------------------------------------------------------------------------
newtype Doc = D (PMode -> P.Doc)

-- | Lift stuff from Hughes & SPJ library
-- ----------------------------------------------------------------------------

boldColorDoc :: Color -> Doc -> Doc
boldColorDoc col d = colorDoc bold (colorDoc col d)

colorDoc :: Color -> Doc -> Doc
colorDoc (Color col) (D doc) = D $ \mode -> case mode of
  Plain               -> doc mode
  ColorMode (Color c) ->   P.zeroWidthText col
                      P.<> doc (ColorMode (Color col))
                      P.<> P.zeroWidthText c -- reset the previous color

liftDoc :: P.Doc -> Doc
liftDoc d = D (\_ -> d)

liftFun :: (a -> P.Doc) -> (a -> Doc)
liftFun f x = D $ \_ -> f x

liftUnaryOp :: (P.Doc -> P.Doc) -> (Doc -> Doc)
liftUnaryOp op (D d) = D (\m -> op (d m))

liftBinaryOp :: (P.Doc -> P.Doc -> P.Doc) -> (Doc -> Doc -> Doc)
liftBinaryOp op (D d1) (D d2) = D (\m -> d1 m `op` d2 m)

liftListOp :: ([P.Doc] -> P.Doc) -> ([Doc] -> Doc)
liftListOp f docs = D (\m -> f [d m | D d <- docs])

-- | Binary combinators
-- ----------------------------------------------------------------------------
(<>), (<+>), ($$), ($+$) :: Doc -> Doc -> Doc
(<>)  = liftBinaryOp (P.<>)
(<+>) = liftBinaryOp (P.<+>)
($$)  = liftBinaryOp (P.$$)
($+$) = liftBinaryOp (P.$+$)

infixl 6 <>, <+>
infixl 5 $$, $+$

-- | List combinators
-- ----------------------------------------------------------------------------
hcat, hsep, vcat, sep, cat, fsep, fcat :: [Doc] -> Doc
hcat = liftListOp P.hcat
hsep = liftListOp P.hsep
vcat = liftListOp P.vcat
sep  = liftListOp P.sep
cat  = liftListOp P.cat
fsep = liftListOp P.fsep
fcat = liftListOp P.fcat

-- ----------------------------------------------------------------------------
parens, brackets, braces, quotes, doubleQuotes :: Doc -> Doc
parens       = liftUnaryOp P.parens
brackets     = liftUnaryOp P.brackets
braces       = liftUnaryOp P.braces
quotes       = liftUnaryOp P.quotes
doubleQuotes = liftUnaryOp P.doubleQuotes

-- | Wrap it if..
-- ----------------------------------------------------------------------------
maybeParens, maybeBrackets, maybeBraces,
  maybeQuotes, maybeDoubleQuotes :: Bool -> Doc -> Doc
maybeParens       b = if b then parens       else id
maybeBrackets     b = if b then brackets     else id
maybeBraces       b = if b then braces       else id
maybeQuotes       b = if b then quotes       else id
maybeDoubleQuotes b = if b then doubleQuotes else id

-- | Some usual combinators
-- ----------------------------------------------------------------------------
nest :: Int -> Doc -> Doc
nest i (D d) = D (\m -> P.nest i (d m))

hang :: Doc -> Int -> Doc -> Doc
hang d1 n d2 = vcat [d1, nest n d2]

-- my version: lenngth 2n-1
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _s []     = []
punctuate _s [d]    = [d]
punctuate  s (d:ds) = (d <> s) : punctuate s ds

-- | Transform basic types
-- ----------------------------------------------------------------------------
text :: String -> Doc
text = liftFun P.text

int :: Int -> Doc
int = liftFun P.int

integer :: Integer -> Doc
integer = liftFun P.integer

rational :: Rational -> Doc
rational = liftFun P.rational

double :: Double -> Doc
double = liftFun P.double

float :: Float -> Doc
float = liftFun P.float

char :: Char -> Doc
char = liftFun P.char

-- | Usual separators and other symbols
-- ----------------------------------------------------------------------------
empty :: Doc
empty = liftDoc P.empty

blankLine :: Doc
blankLine = text ""

semi, comma, colon, space, equals :: Doc
semi   = liftDoc P.semi
comma  = liftDoc P.comma
space  = liftDoc P.space
equals = colorDoc yellow $ liftDoc P.equals
colon  = colorDoc yellow $ liftDoc P.colon

lparen, rparen, lbrack, rbrack, lbrace, rbrace :: Doc
lparen = liftDoc P.lparen
rparen = liftDoc P.rparen
lbrack = liftDoc P.lbrack
rbrack = liftDoc P.rbrack
lbrace = liftDoc P.lbrace
rbrace = liftDoc P.rbrace

underscore, dcolon, arrow, darrow, dot, backslash :: Doc
underscore = liftDoc (P.char '_')
dcolon     = colorDoc yellow $ liftDoc (P.text "::")
arrow      = colorDoc yellow $ liftDoc (P.text "->")
darrow     = colorDoc yellow $ liftDoc (P.text "=>")
dot        = colorDoc yellow $ liftDoc (P.char '.')
backslash  = colorDoc yellow $ liftDoc (P.char '\\')

-- | Rendering Docs
-- ----------------------------------------------------------------------------

-- | The default: No colors
render :: Doc -> String
render (D doc) = P.render (doc Plain)

-- | Render an error (assume colors are on for now :P)
renderError :: Doc -> String
renderError doc = renderWithColor (colorDoc red (text "Error:") <+> doc)

-- | Render in full color!
renderWithColor :: Doc -> String
renderWithColor d = renderWithMode (colorMode reset) d ++ "\27[0m"

-- | Render with option
renderWithMode :: PMode -> Doc -> String
renderWithMode mode (D d) = P.render (d mode)

-- | Pretty Printing Modes
-- ----------------------------------------------------------------------------
data PMode = Plain | ColorMode Color

colorMode :: Color -> PMode
colorMode = ColorMode

plainMode :: PMode
plainMode = Plain

-- | Colors
-- ----------------------------------------------------------------------------
newtype Color = Color String

-- | Reset the color
reset :: Color
reset = Color "\27[0m"

-- | Just in case
bold :: Color
bold = Color "\27[;1m"

-- | Available colors
red, green, yellow, blue, purple, turquoise, white, gray :: Color
red       = Color "\27[31m"
green     = Color "\27[32m"
yellow    = Color "\27[33m"
blue      = Color "\27[34m"
purple    = Color "\27[35m"
turquoise = Color "\27[36m"
white     = Color "\27[37m"
gray      = Color "\27[30m"

-- | The PrettyPrint class
-- ----------------------------------------------------------------------------
class PrettyPrint a where
  ppr :: a -> Doc
  needsParens :: a -> Bool

pprPar :: PrettyPrint a => a -> Doc
pprPar x | needsParens x = parens (ppr x)
         | otherwise     = ppr x

instance PrettyPrint Int where
  ppr           = int
  needsParens _ = False

instance PrettyPrint Char where
  ppr           = char
  needsParens _ = False

instance PrettyPrint Float where
  ppr           = float
  needsParens _ = False

instance PrettyPrint Double where
  ppr           = double
  needsParens _ = False

instance PrettyPrint Bool where
  ppr True      = text "True"
  ppr False     = text "False"
  needsParens _ = False

instance PrettyPrint a => PrettyPrint [a] where
  ppr           = brackets . fsep . punctuate comma . map ppr
  needsParens _ = False

instance PrettyPrint () where
  ppr ()        = text "()"
  needsParens _ = False

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a,b) where
  ppr (x, y)    = parens (ppr x <> comma <> ppr y)
  needsParens _ = False

instance (PrettyPrint a, PrettyPrint b, PrettyPrint c) => PrettyPrint (a,b,c) where
  ppr (x, y, z) = parens (ppr x <> comma <> ppr y <> comma <> ppr z)
  needsParens _ = False

instance PrettyPrint a => PrettyPrint (Maybe a) where
  ppr Nothing  = text "Nothing"
  ppr (Just x) = text "Just" <+> parens (ppr x)
  needsParens  = isJust

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
  ppr (Left  x) = text "Left"  <+> parens (ppr x)
  ppr (Right y) = text "Right" <+> parens (ppr y)
  needsParens _ = True
