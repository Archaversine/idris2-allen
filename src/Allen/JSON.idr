module Allen.JSON

import Allen.Types
import Allen.Interval
import Allen.Relation

import public JSON.Derive

%default total

%language ElabReflection

-- TODO: Use the universe design pattern to make a dependently typed version of this
-- for more powerful JSON parsing
||| A JSON representation of a relation between two intervals
public export
record RelationJSON where 
    constructor MkRelationJSON
    from : String
    to   : String
    rels : String

%runElab derive "RelationJSON" [Show,Eq,ToJSON,FromJSON]

||| A JSON representation of a network of intervals and relations
public export 
record NetworkJSON where 
    constructor MkNetworkJSON
    intervals : List String 
    relations : List RelationJSON

%runElab derive "NetworkJSON" [Show,Eq,ToJSON,FromJSON]

||| Parse a network JSON string
export 
parseNetwork : String -> Either DecodingErr NetworkJSON
parseNetwork = decode

||| Encode a network JSON object to a string
export
encodeNetwork : NetworkJSON -> String
encodeNetwork = encode

||| Add a list of intervals to the network
addIntervals : Ord k => List k -> Allen k ()
addIntervals []        = pure ()
addIntervals (x :: xs) = interval_ x *> addIntervals xs

||| Convert a character to a relation bitset if it is a valid relation char
charToBits : Char -> Either Char RelationBits 
charToBits c with (isRelation c)
  charToBits c | (Yes prf)   = pure (toBits prf)
  charToBits c | (No contra) = Left c

||| Convert a string to a relation bitset if all characters are valid relation chars
export
stringToBits : String -> Either Char RelationBits
stringToBits xs = do 
    thing <- traverse charToBits (unpack xs)
    pure (relationUnion thing)

||| Add a list of relations to the network
export
addRelations : List (RelationJSON) -> Allen String ()
addRelations []        = pure ()
addRelations (x :: xs) = case stringToBits x.rels of 
    Left c  => left (InvalidRelation c)
    Right r => assumeBits x.from r x.to *> addRelations xs

||| Convert a network JSON to an Allen network
export 
loadNetwork : NetworkJSON -> Allen String ()
loadNetwork network = addIntervals network.intervals *> addRelations network.relations

||| Convert an interval to a list of relation JSON objects
intervalToRelations : Interval String -> List RelationJSON
intervalToRelations iv = do 
    (iv2, r) <- Data.SortedMap.toList iv.relations
    let rel = pack (map fst (fromBits r))
    pure (MkRelationJSON iv.intervalID iv2 rel)

||| Convert an Allen graph to a network JSON object
export
graphToNetwork : IntervalGraph String -> NetworkJSON
graphToNetwork g = MkNetworkJSON (keys g) (concatMap intervalToRelations (map snd $ Data.SortedMap.toList g))
