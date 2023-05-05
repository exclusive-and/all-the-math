
module Semigroup

import Equality
import Magma
import Sets

%hide Prelude.Algebra.Semigroup


-- |
-- The proposition that a binary operation is associative.
--
public export
IsAssociative : {t : Type} -> (t -> t -> t) -> Type
IsAssociative {t} m =
    (x : t) -> (y : t) -> (z : t) -> Id (m x (m y z)) (m (m x y) z)

-- |
-- Algebraic laws of semigroups.
-- 
public export
interface IsMagma f => IsSemigroup (f : Type -> Type) where
    -- |
    -- The operation of the semigroup must be associative.
    -- 
    isAssociative   : (m : f t) -> IsAssociative (operation m)


-- |
-- The trivial semigroup type.
-- 
public export
record Semigroup (t : Type) where
    constructor MkSemigroup
    semigroup_carrier       : Set t
    semigroup_operation     : t -> t -> t
    semigroup_isClosed      : IsClosed semigroup_carrier semigroup_operation
    semigroup_isAssociative : IsAssociative semigroup_operation

public export
IsMagma Semigroup where
    carrier     = semigroup_carrier
    operation   = semigroup_operation
    isClosed    = semigroup_isClosed

public export
IsSemigroup Semigroup where
    isAssociative = semigroup_isAssociative
