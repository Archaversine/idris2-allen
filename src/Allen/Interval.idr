module Allen.Interval

import Allen.Types
import Allen.Relation

import Control.Monad.State

import Data.Bits
import Data.List
import Data.List.Quantifiers

%default total

||| Create a new interval 
||| Returns the name of the interval for convenience
export
interval : Ord k => k -> Allen k k
interval name = do 
    otherNames <- gets keys
    others     <- traverse fromID otherNames

    let relations = fromList [(iv, AllRelationBits) | iv <- otherNames]

    modify $ map (\iv => { relations := insert name AllRelationBits iv.relations } iv)
    modify $ insert name (MkInterval name relations)

    pure name

||| Create a new interval without returning the name
export 
interval_ : Ord k => k -> Allen k () 
interval_ name = interval name *> pure ()

||| Return the number of intervals in the network
export 
intervalCount : Allen k Nat 
intervalCount = gets (length . keys)

||| Purely add a relation between two intervals 
||| NOTE: This does not propogate or add the inverse relation to the other interval
export 
setRelation : Interval k -> RelationBits -> k -> Interval k
setRelation i r iv2 = { relations := insert iv2 r i.relations } i

||| Return the set of all posible relations between two intervals in a bit representation
export 
getConstraints : k -> k -> Allen k RelationBits
getConstraints iv1 iv2 = do 
    a <- fromID iv1 
    case lookup iv2 a.relations of 
        Just rs => pure rs
        Nothing => left (MissingInterval iv2)

||| Return a list of all interval names in the network
export 
allIntervals : Allen k (List k)
allIntervals = gets keys

||| Return a list of all interval names in the network except for any in the given list
export
allIntervalsExcept : Eq k => List k -> Allen k (List k)
allIntervalsExcept except = do 
    allIntervals <- gets keys 
    pure [i | i <- allIntervals, not (i `elem` except)]

propogate'' : Eq k => (k, k) -> StateT (List (k, k)) (Allen k) () 
propogate'' (i, j) = do 
    range <- lift $ allIntervalsExcept [i, j]

    flip traverse_ range $ \k => do 
        ki <- lift $ getConstraints k i
        ij <- lift $ getConstraints i j

        let constraints = compose ki ij

        nkj <- lift $ getConstraints k j

        let rkj = nkj .&. constraints

        -- If rkj is a proper subset of nkj, then add (k, j) to the queue
        when (((rkj .|. nkj) == nkj) && (rkj < nkj)) $ do 
            modify ((k, j) ::)

        intervalK <- lift $ fromID k
        lift $ modify $ insert k (setRelation intervalK rkj j)

    flip traverse_ range $ \k => do 
        ij <- lift $ getConstraints i j
        jk <- lift $ getConstraints j k

        let constraints = compose ij jk

        nik <- lift $ getConstraints i k

        let rik = nik .&. constraints

        -- If rik is a proper subset of nik, then add (i, k) to the queue
        when (((rik .|. nik) == nik) && (rik < nik)) $ do 
            modify ((i, k) ::)
        
        intervalI <- lift $ fromID i
        lift $ modify $ insert i (setRelation intervalI rik k)

propogate' : Eq k => StateT (List (k, k)) (Allen k) ()
propogate' = do 
    toDo <- get
    case toDo of 
        [] => pure ()
        ((i, j)::_) => do 
            modify (drop 1) -- Remove the first element from the queue
            propogate'' (i, j)
            propogate'' (j, i)
            assert_total propogate'
||| Propogate the relations between two intervals to all other intervals
propogate : Eq k => (k, k) -> Allen k ()
propogate r = evalStateT [r] propogate'

||| Set relations between two intervals with bits (this propogates)
export
assumeBits : Eq k => k -> RelationBits -> k -> Allen k () 
assumeBits iv1 bits iv2 = do 
    a <- fromID iv1 
    b <- fromID iv2 

    modify $ insert iv1 (setRelation a bits iv2)
    modify $ insert iv2 (setRelation b (converse bits) iv1)

    propogate (iv1, iv2)

||| Set a relation between two intervals (this propogates)
export
assume : Eq k => k -> Relation c -> k -> Allen k ()
assume iv1 r iv2 = assumeBits iv1 (toBits r) iv2

||| Set a list of relations between two intervals (this propogates)
export
assumeList : Eq k => k -> List (c : Char ** Relation c) -> k -> Allen k () 
assumeList iv1 rs iv2 = assumeBits iv1 (relationUnion [toBits r | (_ ** r) <- rs]) iv2

||| Set a list of relations between two intervals with a list of chars (this propogates)
export
assumeChars : Eq k => k -> (xs : List Char) -> {auto 0 prf : All Relation xs} -> k -> Allen k () 
assumeChars iv1 xs iv2 = assumeBits iv1 (bitsFromChars xs) iv2

||| Set a list of relations between two intervals with a string (this propogates)
export 
assumeString : Eq k => k -> (s : String) -> {auto 0 prf : All Relation (unpack s)} -> k -> Allen k ()
assumeString iv1 s iv2 = assumeChars iv1 (unpack s) iv2