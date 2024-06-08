module Allen.Relation

import Allen.Types

import Data.Bits
import Data.List
import Data.Vect
import Data.So

import public Data.List.Quantifiers

%default total

||| All possible allen relations in Vect
public export 
allRelations : Vect 13 (c : Char ** Relation c)
allRelations = [ ('p' ** Precedes)
               , ('m' ** Meets)
               , ('o' ** Overlaps)
               , ('F' ** FinishedBy)
               , ('D' ** Contains)
               , ('s' ** Starts)
               , ('e' ** Equals)
               , ('S' ** StartedBy)
               , ('d' ** During)
               , ('f' ** Finishes)
               , ('O' ** OverlappedBy)
               , ('M' ** MetBy)
               , ('P' ** PrecededBy)
               ]

||| Determine if a char has a corresponding relation.
||| Returns a proof that the char is a relation or a proof that it is not.
export
isRelation : (c : Char) -> Dec (Relation c)
isRelation 'p' = Yes Precedes
isRelation 'm' = Yes Meets
isRelation 'o' = Yes Overlaps
isRelation 'F' = Yes FinishedBy
isRelation 'D' = Yes Contains
isRelation 's' = Yes Starts
isRelation 'e' = Yes Equals
isRelation 'S' = Yes StartedBy
isRelation 'd' = Yes During
isRelation 'f' = Yes Finishes
isRelation 'O' = Yes OverlappedBy
isRelation 'M' = Yes MetBy
isRelation 'P' = Yes PrecededBy
isRelation x   = assert_total $ No (\case Refl impossible)

%inline
asList : Vect n a -> List a 
asList []        = []
asList (x :: xs) = x :: asList xs


||| All possible allen relations in a list format
%inline
public export 
AllRelationsList : List (c : Char ** Relation c)
AllRelationsList = asList allRelations

relationNumber : Relation c -> Nat
relationNumber Precedes     = 0
relationNumber Meets        = 1
relationNumber Overlaps     = 2
relationNumber FinishedBy   = 3
relationNumber Contains     = 4
relationNumber Starts       = 5
relationNumber Equals       = 6
relationNumber StartedBy    = 7
relationNumber During       = 8
relationNumber Finishes     = 9
relationNumber OverlappedBy = 10
relationNumber MetBy        = 11
relationNumber PrecededBy   = 12

||| Convert a relation to its bit representation
%inline
export
toBits : Relation c -> RelationBits 
toBits Precedes     = 1
toBits Meets        = 2
toBits Overlaps     = 4
toBits FinishedBy   = 8
toBits Contains     = 16
toBits Starts       = 32
toBits Equals       = 64
toBits StartedBy    = 128
toBits During       = 256
toBits Finishes     = 512
toBits OverlappedBy = 1024
toBits MetBy        = 2048
toBits PrecededBy   = 4096

||| Bit representation of all possible relations
export 
AllRelationBits : RelationBits 
AllRelationBits = foldl (.|.) 0 [toBits r | (c ** r) <- AllRelationsList]

||| Combine multiple relation bits via bitwise or
%inline
public export
relationUnion : List RelationBits -> RelationBits
relationUnion = foldl (.|.) 0

||| Combine multiple relations via bitwise and 
%inline 
export 
relationIntersection : List RelationBits -> RelationBits 
relationIntersection = foldl (.&.) AllRelationBits

||| A proof that intersection with all relations is the same as the original relation
export
0 relInterFullIdentity : (r : Relation c) -> relationIntersection [toBits r, AllRelationBits] = toBits r
relInterFullIdentity Precedes     = Refl
relInterFullIdentity Meets        = Refl
relInterFullIdentity Overlaps     = Refl
relInterFullIdentity FinishedBy   = Refl
relInterFullIdentity Contains     = Refl
relInterFullIdentity Starts       = Refl
relInterFullIdentity Equals       = Refl
relInterFullIdentity StartedBy    = Refl
relInterFullIdentity During       = Refl
relInterFullIdentity Finishes     = Refl
relInterFullIdentity OverlappedBy = Refl
relInterFullIdentity MetBy        = Refl
relInterFullIdentity PrecededBy   = Refl

||| A proof that the intersection of all relations and all relations is all relations
export
0 relInterFullFull : relationIntersection [AllRelationBits, AllRelationBits] = AllRelationBits
relInterFullFull = Refl

||| A proof that the intersection of anything and the empty set is the empty set 
export 
0 relInterEmpty : relationIntersection [AllRelationBits, 0] = 0
relInterEmpty = Refl

||| Cast relation bits to a set of relations
%inline
export
fromBits : RelationBits -> List (c : Char ** Relation c)
fromBits bs = [dp | dp@(c ** r) <- asList allRelations, toBits r .&. bs /= 0]

||| A proof that casting a relation to bits and then back loses no information
export
0 singleBitProof : (r : Relation c) -> fromBits (toBits r) = [(c ** r)]
singleBitProof Precedes     = Refl
singleBitProof Meets        = Refl
singleBitProof Overlaps     = Refl
singleBitProof FinishedBy   = Refl
singleBitProof Contains     = Refl
singleBitProof Starts       = Refl
singleBitProof Equals       = Refl
singleBitProof StartedBy    = Refl
singleBitProof During       = Refl
singleBitProof Finishes     = Refl
singleBitProof OverlappedBy = Refl
singleBitProof MetBy        = Refl
singleBitProof PrecededBy   = Refl

||| A proof that converting all relations to bits and back loses no information
export
0 allBitsProof : fromBits (foldl (.|.) 0 [toBits r | (c ** r) <- AllRelationsList]) = AllRelationsList
allBitsProof = Refl

||| Convert a char to it's corresponding Relation.
export
charToRelation : (c : Char) -> {auto 0 prf : Relation c} -> Relation c 
charToRelation 'p' @{Precedes}     = Precedes
charToRelation 'm' @{Meets}        = Meets
charToRelation 'o' @{Overlaps}     = Overlaps
charToRelation 'F' @{FinishedBy}   = FinishedBy
charToRelation 'D' @{Contains}     = Contains
charToRelation 's' @{Starts}       = Starts
charToRelation 'e' @{Equals}       = Equals
charToRelation 'S' @{StartedBy}    = StartedBy
charToRelation 'd' @{During}       = During
charToRelation 'f' @{Finishes}     = Finishes
charToRelation 'O' @{OverlappedBy} = OverlappedBy
charToRelation 'M' @{MetBy}        = MetBy
charToRelation 'P' @{PrecededBy}   = PrecededBy
charToRelation _ = assert_total (idris_crash "impossible")

||| Convert a relation into its corresponding character
%inline
export
relationToChar : {c : Char} -> Relation c -> Char 
relationToChar = const c

||| A proof that relationtoChar actually returns the correct char
0 relationToCharProof : (c : Char) -> {auto 0 prf : Relation c} -> c = relationToChar prf
relationToCharProof 'p' @{Precedes}     = Refl
relationToCharProof 'm' @{Meets}        = Refl
relationToCharProof 'o' @{Overlaps}     = Refl
relationToCharProof 'F' @{FinishedBy}   = Refl
relationToCharProof 'D' @{Contains}     = Refl
relationToCharProof 's' @{Starts}       = Refl
relationToCharProof 'e' @{Equals}       = Refl
relationToCharProof 'S' @{StartedBy}    = Refl
relationToCharProof 'd' @{During}       = Refl
relationToCharProof 'f' @{Finishes}     = Refl
relationToCharProof 'O' @{OverlappedBy} = Refl
relationToCharProof 'M' @{MetBy}        = Refl
relationToCharProof 'P' @{PrecededBy}   = Refl
relationToCharProof _ = assert_total (idris_crash "impossible")

||| For any char that has a corresponding Relation, return it's converse
0 converseChar : (c : Char) -> {auto 0 prf : Relation c} -> Char
converseChar 'p' @{Precedes}     = 'P'
converseChar 'm' @{Meets}        = 'M'
converseChar 'o' @{Overlaps}     = 'O'
converseChar 'F' @{FinishedBy}   = 'f'
converseChar 'D' @{Contains}     = 'd'
converseChar 's' @{Starts}       = 'S'
converseChar 'e' @{Equals}       = 'e'
converseChar 'S' @{StartedBy}    = 's'
converseChar 'd' @{During}       = 'D'
converseChar 'f' @{Finishes}     = 'F'
converseChar 'O' @{OverlappedBy} = 'o'
converseChar 'M' @{MetBy}        = 'm'
converseChar 'P' @{PrecededBy}   = 'p'
converseChar _ = assert_total (idris_crash "impossible")

||| A lemma proving that the converse char from the converseChar function always has a 
||| corresponding allen relation
0 converseCharProof : (c : Char) -> {auto 0 prf : Relation c} -> Relation (converseChar c)
converseCharProof 'p' @{Precedes}     = PrecededBy
converseCharProof 'm' @{Meets}        = MetBy
converseCharProof 'o' @{Overlaps}     = OverlappedBy
converseCharProof 'F' @{FinishedBy}   = Finishes
converseCharProof 'D' @{Contains}     = During
converseCharProof 's' @{Starts}       = StartedBy
converseCharProof 'e' @{Equals}       = Equals
converseCharProof 'S' @{StartedBy}    = Starts
converseCharProof 'd' @{During}       = Contains
converseCharProof 'f' @{Finishes}     = FinishedBy
converseCharProof 'O' @{OverlappedBy} = Overlaps
converseCharProof 'M' @{MetBy}        = Meets
converseCharProof 'P' @{PrecededBy}   = Precedes
converseCharProof _ = assert_total (idris_crash "impossible")

||| A proof that the converse of the converse always returns the original for 
||| any given relation
export
0 converseProof : (c : Char) 
    -> (0 prf : Relation c)
    -> c = converseChar @{(converseCharProof c)} (converseChar c)
converseProof 'p' Precedes     = Refl
converseProof 'm' Meets        = Refl
converseProof 'o' Overlaps     = Refl
converseProof 'F' FinishedBy   = Refl
converseProof 'D' Contains     = Refl
converseProof 's' Starts       = Refl
converseProof 'e' Equals       = Refl
converseProof 'S' StartedBy    = Refl
converseProof 'd' During       = Refl
converseProof 'f' Finishes     = Refl
converseProof 'O' OverlappedBy = Refl
converseProof 'M' MetBy        = Refl
converseProof 'P' PrecededBy   = Refl
converseProof _ _ = assert_total (idris_crash "impossible")

||| For any relation return its converse
%inline
export 
converseR : Relation c -> Relation (converseChar c)
converseR Precedes     = PrecededBy
converseR Meets        = MetBy
converseR Overlaps     = OverlappedBy
converseR FinishedBy   = Finishes
converseR Contains     = During
converseR Starts       = StartedBy
converseR Equals       = Equals
converseR StartedBy    = Starts
converseR During       = Contains
converseR Finishes     = FinishedBy
converseR OverlappedBy = Overlaps
converseR MetBy        = Meets
converseR PrecededBy   = Precedes

||| Find the converse of a set of relations in their bit representation
%inline
export 
converse : RelationBits -> RelationBits
converse bits = relationUnion [toBits (converseR r) | (c ** r) <- fromBits bits]

||| A proof that the converse of the converse of a set of relations is the original set
export
0 converseAllBits : converse AllRelationBits = AllRelationBits
converseAllBits = Refl

||| Test that a specified set of relations is a subset of a relations between 
||| two intervals.
export 
testRelationBits : RelationBits -> k -> k -> Allen k Bool 
testRelationBits bits iv1 iv2 = do 
    a <- relations <$> fromID iv1 
    x <- case lookup iv2 a of 
        Just bs => pure bs 
        Nothing => left (MissingRelations iv1 iv2)

    pure (bits .&. x == bits)

||| Check that a relation is present between two intervals
export 
testRelation : Relation c -> k -> k -> Allen k Bool
testRelation r iv1 iv2 = testRelationBits (toBits r) iv1 iv2

||| Check that a list of relations is a subset between the set of relations between two intervals
export 
testRelations : List (c : Char ** Relation c) -> k -> k -> Allen k Bool 
testRelations rs iv1 iv2 = testRelationBits (relationUnion [toBits r | (c ** r) <- rs]) iv1 iv2

||| Parse a list of chars into a set of relations represented as bits
export
bitsFromChars : (xs : List Char) -> {auto 0 prf : All Relation xs} -> RelationBits
bitsFromChars []        @{[]}          = 0
bitsFromChars (x :: xs) @{(px :: pxs)} = toBits (charToRelation x) .|. bitsFromChars xs

||| Parse a string into a set of relations represented as bits
export 
bitsFromString : (s : String) -> {auto 0 prf : All Relation (unpack s)} -> RelationBits
bitsFromString xs = bitsFromChars (unpack xs)

||| Parse a list of strings into a list of relation sets represented as bits
bitsFromTable : (xs : List String) -> {auto 0 prf : All (\x => All Relation (unpack x)) xs} -> List RelationBits
bitsFromTable []        @{[]}          = []
bitsFromTable (x :: xs) @{(px :: pxs)} = bitsFromString x :: bitsFromTable xs

||| String representation of the set of all relations
public export 
Full : String 
Full = "pmoFDseSdfOMP"

||| String representation of the set of all relations except for pmMP
public export
Concur : String 
Concur = "oFDseSdfO"

||| A proof that bitsFromString of Full is equal to the set of all relations
export
0 bitsFromStringFullPrf : bitsFromString Full = relationUnion [toBits r | (c ** r) <- AllRelationsList]
bitsFromStringFullPrf = Refl

-- Needed because ComposeLookup is a big list
-- TODO: Replace this with HDec0, which is more efficient
%auto_implicit_depth 175

||| Composition table of all relations
||| Table referenced from here: https://www.ics.uci.edu/~alspaugh/cls/shr/allen.html
ComposeLookup : List RelationBits
ComposeLookup = bitsFromTable table 
--                |    p   |    m   |   o     |  F     |  D     |  s     |  e |   S    |     d   |    f   |     O   |    M   |    P
-- ---------------+--------+--------+---------+--------+--------+--------+----+--------+---------+--------+---------+--------+-------------
    where table : List String 
          table = [     "p",     "p",      "p",     "p",     "p",     "p", "p",     "p",  "pmosd", "pmosd",  "pmosd", "pmosd",    Full -- p
                  ,     "p",     "p",      "p",     "p",     "p",     "m", "m",     "m",    "osd",   "osd",    "osd",   "Fef", "DSOMP" -- m
                  ,     "p",     "p",    "pmo",   "pmo", "pmoFD",     "o", "o",   "oFD",    "osd",   "osd",   Concur,   "DSO", "DSOMP" -- o
                  ,     "p",     "m",      "o",     "F",     "D",     "o", "F",     "D",    "osd",   "Fef",    "DSO",   "DSO", "DSOMP" -- F
                  , "pmoFD",   "oFD",    "oFD",     "D",     "D",   "oFD", "D",     "D",   Concur,   "DSO",    "DSO",   "DSO", "DSOMP" -- D
                  ,     "p",     "p",    "pmo",   "pmo", "pmoFD",     "s", "s",   "seS",      "d",     "d",    "dfO",     "M",     "P" -- s
                  ,     "p",     "m",      "o",     "F",     "D",     "s", "e",     "S",      "d",     "f",      "O",     "M",     "P" -- e
                  , "pmoFD",   "oFD",    "oFD",     "D",     "D",   "seS", "S",     "S",    "dfO",     "O",      "O",     "M",     "P" -- S
                  ,     "p",     "p",  "pmosd", "pmosd",    Full,     "d", "d", "dfOMP",      "d",     "d",  "dfOMP",     "P",     "P" -- d
                  ,     "p",     "m",    "osd",   "Fef", "DSOMP",     "d", "f",   "OMP",      "d",     "f",    "OMP",     "P",     "P" -- f
                  , "pmoFD",   "oFD",   Concur,   "DSO", "DSOMP",   "dfO", "O",   "OMP",    "dfO",     "O",    "OMP",     "P",     "P" -- O
                  , "pmoFD",   "seS",    "dfO",     "M",     "P",   "dfO", "M",     "P",    "dfO",     "M",      "P",     "P",     "P" -- M
                  ,    Full, "dfOMP", "dfOMOP",     "P",     "P", "dfOMP", "P",     "P",  "dfOMP",     "P",      "P",     "P",     "P" -- P
                  ]

%auto_implicit_depth 50

--composeLength : length ComposeLookup = 13 * 13
--composeLength = Refl

||| Compose two relations together and return the list of corresponding relations
export
composeR : Relation c1 -> Relation c2 -> List (c : Char ** Relation c)
composeR x y with (13 * relationNumber x + relationNumber y)
  composeR x y | location with (inBounds location ComposeLookup)
    composeR x y | location | (Yes prf)   = fromBits (index location ComposeLookup)
    composeR x y | location | (No contra) = []

||| Compose two relations together and return the bit representation of the output
export
composeRBits : Relation c1 -> Relation c2 -> RelationBits 
composeRBits x y = relationUnion [toBits r | (_ ** r) <- composeR x y]

||| A proof that composing with Equals on the right side is the identity
export
0 composeEqRhs : (r : Relation c) -> composeR r Equals = [(c ** r)]
composeEqRhs Precedes     = Refl
composeEqRhs Meets        = Refl
composeEqRhs Overlaps     = Refl
composeEqRhs FinishedBy   = Refl
composeEqRhs Contains     = Refl
composeEqRhs Starts       = Refl
composeEqRhs Equals       = Refl
composeEqRhs StartedBy    = Refl
composeEqRhs During       = Refl
composeEqRhs Finishes     = Refl
composeEqRhs OverlappedBy = Refl
composeEqRhs MetBy        = Refl
composeEqRhs PrecededBy   = Refl

||| A proof that composing with Equals on the left side is the identity
export
0 composeEqLhs : (r : Relation c) -> composeR Equals r = [(c ** r)]
composeEqLhs Precedes     = Refl
composeEqLhs Meets        = Refl
composeEqLhs Overlaps     = Refl
composeEqLhs FinishedBy   = Refl
composeEqLhs Contains     = Refl
composeEqLhs Starts       = Refl
composeEqLhs Equals       = Refl
composeEqLhs StartedBy    = Refl
composeEqLhs During       = Refl
composeEqLhs Finishes     = Refl
composeEqLhs OverlappedBy = Refl
composeEqLhs MetBy        = Refl
composeEqLhs PrecededBy   = Refl

||| Compose two sets of relations together 
export
compose : RelationBits -> RelationBits -> RelationBits
compose r1 r2 = relationUnion [composeRBits a b | (_ ** a) <- fromBits r1, (_ ** b) <- fromBits r2]
