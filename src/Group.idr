
module Group

import Equality
import Magma
import Monoid
import Semigroup
import Sets

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.(-)


-- |
-- The proposition that a set contains an inverse for each of its
-- elements.
-- 
public export
HasInverses : {t : Type} -> Set t -> (t -> t) -> Type
HasInverses {t} s inv = (x : t) -> s x -> s (inv x)

-- |
-- The proposition that the inverse function really does produce
-- left-inverses for each element.
-- 
public export
IsInverse : {t : Type} -> t -> (t -> t -> t) -> (t -> t) -> Type
IsInverse {t} e m inv = (x : t) -> Id (m (inv x) x) e

-- |
-- Algebraic laws of groups.
-- 
public export
interface IsMonoid f => IsGroup (f : Type -> Type) where
    -- |
    -- A group must have a function which sends each element to
    -- its inverse.
    -- 
    invert      : f t -> t -> t

    -- |
    -- The carrier set of the group must be closed under taking
    -- inverses.
    -- 
    hasInverses : (m : f t) -> HasInverses (carrier m) (invert m)

    -- |
    -- The invert function must really send an element to its
    -- inverse.
    -- 
    isInverse   : (m : f t)
               -> IsInverse (identity m) (operation m) (invert m)


-- |
-- The trivial group type.
-- 
public export
record Group (t : Type) where
    constructor MkGroup
    group_carrier       : Set t
    group_operation     : t -> t -> t
    group_isClosed      : IsClosed group_carrier group_operation
    group_isAssociative : IsAssociative group_operation
    group_identity      : t
    group_hasIdentity   : group_carrier group_identity
    group_isIdentity    : IsIdentity group_identity group_operation
    group_invert        : t -> t
    group_hasInverses   : HasInverses group_carrier group_invert
    group_isInverse     : IsInverse group_identity group_operation group_invert

public export
IsMagma Group where
    carrier     = group_carrier
    operation   = group_operation
    isClosed    = group_isClosed

public export
IsSemigroup Group where
    isAssociative = group_isAssociative

public export
IsMonoid Group where
    identity    = group_identity
    hasIdentity = group_hasIdentity
    isIdentity  = group_isIdentity

public export
IsGroup Group where
    invert      = group_invert
    hasInverses = group_hasInverses
    isInverse   = group_isInverse

