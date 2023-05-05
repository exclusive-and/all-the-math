
module Monoid

import Equality
import Magma
import Semigroup
import Sets

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


-- |
-- The proposition that a value is a left-identity for a binary
-- operation.
-- 
public export
IsIdentity : {t : Type} -> t -> (t -> t -> t) -> Type
IsIdentity {t} e m = (x : t) -> Id (m e x) x

-- |
-- Algebraic laws of monoids.
-- 
public export
interface IsSemigroup f => IsMonoid (f : Type -> Type) where
    -- |
    -- The element of the monoid to use as the identity.
    -- 
    identity    : f t -> t

    -- |
    -- The identity must be contained in the carrier set.
    -- 
    hasIdentity : (m : f t) -> carrier m (identity m)

    -- |
    -- The identity element must actually be an identity of the
    -- monoid's operation.
    -- 
    isIdentity  : (m : f t) -> IsIdentity (identity m) (operation m)


-- |
-- The trivial monoid type.
-- 
public export
record Monoid (t : Type) where
    constructor MkMonoid
    monoid_carrier       : Set t
    monoid_operation     : t -> t -> t
    monoid_isClosed      : IsClosed monoid_carrier monoid_operation
    monoid_isAssociative : IsAssociative monoid_operation
    monoid_identity      : t
    monoid_hasIdentity   : monoid_carrier monoid_identity
    monoid_isIdentity    : IsIdentity monoid_identity monoid_operation

public export
IsMagma Monoid where
    carrier     = monoid_carrier
    operation   = monoid_operation
    isClosed    = monoid_isClosed

public export
IsSemigroup Monoid where
    isAssociative = monoid_isAssociative

public export
IsMonoid Monoid where
    identity    = monoid_identity
    hasIdentity = monoid_hasIdentity
    isIdentity  = monoid_isIdentity

