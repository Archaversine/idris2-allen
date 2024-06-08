# Idris - Allen's Interval Algebra Implementation

A Re-Implementation of Allen's Interval Algebra in Idris. The original was written in [Haskell](https://github.com/archaversine/allen#readme).
This implementation also takes advantage of Idris's dependent types to completely eliminate the possibility of runtime errors and adds helpful compile-time restrictions for the programmer using the library. It also re-implements the `Allen` monad to allow for 
polymorphic intervals indices. So for example, the previous implementation was restricted to only integers, but this implementation allows for any type to be used as an index.

This library provides a monadic way to perform computations related to Allen's interval algebra. The interval network strucutre is implicitly updated upon the creation of a new interval and when a set of relations is applied to two intervals.

## Sources 

This library is based off of the interval algebra described in
[Maintaining Knowledge about Temporal Intervals](https://cse.unl.edu/~choueiry/Documents/Allen-CACM1983.pdf), 
and [Allen's Interval Algebra](https://www.ics.uci.edu/~alspaugh/cls/shr/allen.html).

## A Simple Example 

Assume a situation with three intervals:

1. I am walking.
2. I am talking.
3. My friend calls me.

and assume that we know the following:

1. When I am walking, I am not talking.
2. When my friend called me, I started talking.

we can easily compute the relations between when I was walking and when my friend called me:

```idris
calc : Allen String (List (c : Char ** Relation c))
calc = do 
    walking <- interval "walking"
    talking <- interval "talking"
    friend  <- interval "friend"

    assumeString walking "pmMP" talking
    assume friend Starts talking

    relations <- getConstraints walking friend

    pure (fromBits relations)

main : IO ()
main = case evalAllen calc of 
    Left e  => putStrLn $ "Error: " ++ show e
    Right x => putStrLn (pack (map fst x))
```

And this gives us the result:

```
pmP
```

Read as: precedes, meets, or is preceded by.

Which means that we can deduce that walking either happens before, directly before, or after my friend calls.

## A Complex Example

Consider the following sentence:

*John was not in the room when I touched the switch to turn on the light.*
 
From this sentence we can derive three intervals ***R***, ***S***, and ***L*** where
***R*** is the time that John was in the room, ***S*** is the time where the light 
switched was touched, and ***L*** the time where the light was on. 

From the sentence, we know at least the following:

- ***S*** overlaps *or* meets ***L**
- ***S*** is before, meets, is met by, or is after ***R***.

To represent this as a reusable network, the following code can be written:

```idris 
network : Allen Char (Char, Char, Char)
network = do 
    r <- interval 'r'
    s <- interval 's'
    l <- interval 'l'

    assumeString s "om" l
    assumeString s "pmMP" r

    pure (r, s, l)
```

If we wanted to learn the possible relations between r and l the following code 
can be used (NOTE that `evalAllen` is used to actually evaluate the calculation):

```idris
relationsRL : List (c : Char ** Relation c)
relationsRL = evalAllen $ do 
    -- Use the previously constructed network
    -- `s` is discarded since it is not used
    (r, _, l) <- network

    -- `getConstraints` returns the bitset of relations
    fromBits <$> getConstraints r l
```

Running the above code, we get the following result:

```
pseSdfOMP
```

Assume that at some point we learn the following extra information:

***L*** overlaps, starts, or is during ***R***.

To calculate the updated relations between ***L*** and ***R*** and between 
***S*** and ***R*** the following code can be used.

```idris
updatedRelations : (List (c : Char ** Relation c), List (c : Char ** Relation c))
updatedRelations = evalAllen $ do 
    (r, s, l) <- network

    assumeString l "sod" r

    lrRelations <- fromBits <$> getConstraints l r 
    srRelations <- fromBits <$> getConstraints s r

    pure (lrRelations, srRelations)
```

This would provide the result:

```
([('o' ** Overlaps), ('s' ** Starts)], [('p' ** Precedes), ('m' ** Meets)])
```

## Documentation 

Documentation to be added soon.

## Calculations as JSON 

For using the allen executable, calculations need to be written in JSON format (they will also be outputted in JSON).
For example, to express a relation between two intervals `a` and `b` where `a` precedes `b`, the following JSON can be used:

```json
{
    "intervals": ["a","b"],
    "relations": [
        {"from":"a","to":"b","rels":"p"}
    ]
}
```

Running the allen executable with 

```
allen file input.json output.json
```

will write the following to `output.json`:

```json
{"intervals":["a","b"],"relations":[{"from":"a","to":"b","rels":"p"},{"from":"b","to":"a","rels":"P"}]}
```

NOTE: When using the JSON functionality, the interval names must be strings. This is planned to be changed in the future to allow 
for more types to be used.