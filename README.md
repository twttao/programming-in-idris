## Programming in Idris



1. Implicit Argument

```haskell
-- explicit
append: (elem: Type) -> (n: Nat) -> (m: Nat) ->
		Vect n elem -> Vect m elem -> Vect (n + m) elem
-- > append Char 2 2 ['a', 'b'] ['c', 'd']
-- > append _ _ _ ['a', 'b'] ['c', 'd']

-- implicit
append: Vect n elem -> Vect m elem -> Vect (n + m) elem		-- unbound
append: {elem: Type} -> {n: Nat} -> {m: Nat} ->
		Vect n elem -> Vect m elem -> Vect (n + m) elem	 	-- bound
-- > append ['a', 'b'] ['c', 'd']
```



2. Use Implicit in Function

```haskell
-- plain
length: Vect n elem -> Nat
length [] = Z
length (x :: xs) = 1 + length xs

-- dependent
length: Vect n elem -> Nat
length {n} xs = n

-- dependent with pattern matching
createEmpties: Vect n (Vect 0 a)
createEmpties {n = Z} = []
createEmpties {n = (S k)} = [] :: createEmpties
```



3. Basic Data Types

```haskell
-- enumerated types (enum)
data Bool = False | True
data Direction = North | East | South | West

-- union types (parameterized enum)
data Shape = Triangle Double Double
			| Rectangle Double Double
			| Circle Double
data Shape: Type where
	Triangle: Double -> Double -> Shape
	Rectangle: Double -> Double -> Shape
	Circle: Double -> Shape
			
-- recursive types (self-defining types)
data Nat = Z | S Nat
data Infinite = Forever Infinite

-- generic types (type-parameterized)
data Maybe valtype = Nothing | Just valtype
data Either a b = Left a | Right b
```



4. Pattern Naming and Reuse

```haskell
insert x orgi@(Node left val right)
	= case compare x val of
		LT => Node (insert x left) val right
		EQ => orig
		GT => Node left val (insert x right)
```



5. Dependent Data Types

```haskell
data PowerSouce = Petrol | Pedal

data Vehicle: PowerSource -> Type where		-- dependent types / families of types
	Bicycle: Vehicle Pedal
	Car: (fuel: Nat) -> Vehicle Petrol
	Bus: (fuel: Nat) -> Vehicle Petrol
	
data Vect: Nat -> Type -> Type where
	Nil: Vect Z a
	(::): (x: a) -> (xs: Vect k a) -> Vect (S k) a
	
data DataStore: Type where
	MkData: (size: Nat) ->
		    (items: Vect size String) ->	-- computation from parameters
		    DataStore
```

