module Sets
  ( Set(Set),
  member,
  )
where
-- A set of some Haskell data type.
data Set w = Set (w -> Bool)

member :: w -> Set w -> Bool
member x (Set pred) = pred x
