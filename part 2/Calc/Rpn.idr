module Rpn

import Data.Vect

%access export

data Op = Plus | Minus | Multiply | Divide

data Action = Operator Op | Operand Double

calc : (actions : Vect n Action) -> (stack : List Double) -> Maybe Double
calc []                          []             = Nothing
calc []                          (x :: [])      = Just x
calc []                          (x :: xs)      = Nothing
calc ((Operand  x)        :: xs) stack          = calc xs (x :: stack)
calc ((Operator Plus)     :: xs) []             = Nothing
calc ((Operator Plus)     :: xs) (x :: [])      = Nothing
calc ((Operator Plus)     :: xs) (x :: y :: ys) = calc xs (y+x :: ys)
calc ((Operator Minus)    :: xs) []             = Nothing
calc ((Operator Minus)    :: xs) (x :: [])      = Nothing
calc ((Operator Minus)    :: xs) (x :: y :: ys) = calc xs (y-x :: ys)
calc ((Operator Multiply) :: xs) []             = Nothing
calc ((Operator Multiply) :: xs) (x :: [])      = Nothing
calc ((Operator Multiply) :: xs) (x :: y :: ys) = calc xs (y*x :: ys)
calc ((Operator Divide)   :: xs) []             = Nothing
calc ((Operator Divide)   :: xs) (x :: [])      = Nothing
calc ((Operator Divide)   :: xs) (x :: y :: ys) = calc xs (y/x :: ys)

parseAction : (word : List Char) -> Maybe Action
parseAction [] = Nothing
parseAction ['+'] = Just $ Operator Plus
parseAction ['-'] = Just $ Operator Minus
parseAction ['*'] = Just $ Operator Multiply
parseAction ['/'] = Just $ Operator Divide
parseAction word = if all isDigit word
                   then Just . Operand . cast $ pack word
                   else Nothing

tokenize : String -> Maybe (List Action)
tokenize = sequence . map (parseAction . unpack) . words

actions : (input : String) -> Maybe (n ** Vect n Action)
actions input = case tokenize input of
                     Nothing => Nothing
                     Just xs => Just (_ ** fromList xs)

calcRpn : (input : String) -> Maybe Double
calcRpn input = case actions input of
                     Nothing        => Nothing
                     Just (_ ** as) => calc as []
