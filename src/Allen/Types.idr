module Allen.Types

import public Control.Monad.Error.Either
import public Control.Monad.State

import Data.String
import public Data.SortedMap

%default total

||| Bit representation of Allen relations where each relation is represented by a single bit
public export
RelationBits : Type 
RelationBits = Bits16

||| A data type representing an interval with a unique identifier and a map of relations
||| to other intervals
public export
record Interval (k : Type) where 
    constructor MkInterval 
    intervalID : k 
    relations  : SortedMap k RelationBits

||| A map where the key is the interval's id and the value is the interval itself
public export
IntervalGraph : Type -> Type
IntervalGraph k = SortedMap k (Interval k)

||| A data type representing the possible errors that can occur when working with Allen intervals
public export
data AllenError k 
    = MissingInterval k 
    | MissingRelations k k 
    | DuplicateInterval k
    | InvalidRelation Char

export 
Show k => Show (AllenError k) where 
    show (MissingInterval x)    = "Missing interval: " ++ show x
    show (MissingRelations x y) = "Missing interval relations: " ++ show x ++ " & " ++ show y
    show (DuplicateInterval x)  = "Duplicate interval: " ++ show x
    show (InvalidRelation x)    = "Invalid relation: " ++ show x

||| The Allen monad for working with Allen intervals
public export 
Allen : Type -> Type -> Type
Allen k = EitherT (AllenError k) (State (IntervalGraph k))

||| Run an Allen computation with an empty interval graph returning the result and the graph
export 
runAllen : Ord k => Allen k a -> (IntervalGraph k, Either (AllenError k) a)
runAllen calc = runState empty (runEitherT calc)

||| Run an Allen computation with an empty interval graph returning the result
export 
evalAllen : Ord k => Allen k a -> Either (AllenError k) a
evalAllen = snd . runAllen

||| Run an Allen computation with a given interval graph returning the graph
export 
execAllen : Ord k => Allen k a -> IntervalGraph k
execAllen = fst . runAllen

||| A depedent type representing the possible Allen relations and their corresponding characters
public export 
data Relation : Char -> Type where 
    Precedes     : Relation 'p'
    Meets        : Relation 'm'
    Overlaps     : Relation 'o'
    FinishedBy   : Relation 'F'
    Contains     : Relation 'D'
    Starts       : Relation 's'
    Equals       : Relation 'e'
    StartedBy    : Relation 'S'
    During       : Relation 'd'
    Finishes     : Relation 'f'
    OverlappedBy : Relation 'O'
    MetBy        : Relation 'M'
    PrecededBy   : Relation 'P'

export
{c : Char} -> Show (Relation c) where 
    show = const (singleton c)

||| A function which returns an interval given a unique identifier
export
fromID : k -> Allen k (Interval k)
fromID key = gets (lookup key) >>= \case 
    Nothing => left (MissingInterval key)
    Just iv => pure iv

