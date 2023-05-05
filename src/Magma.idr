
module Magma

import Sets


-- |
-- The proposition that a set is closed under some binary operation.
-- 
public export
IsClosed : {t : Type} -> Set t -> (t -> t -> t) -> Type
IsClosed {t} s m =
    (x : t) -> (p : s x) -> (y : t) -> (q : s y) -> s (m x y)

-- |
-- Algebraic laws of magmas.
-- 
public export
interface IsMagma (f : Type -> Type) where
    -- |
    -- All magmas must have a carrier set.
    -- 
    carrier     : {t : Type} -> f t -> Set t

    -- |
    -- Magmas have a binary operation.
    -- 
    operation   : f t -> t -> t -> t

    -- |
    -- The carrier set of a magma must be closed under its operation.
    -- 
    isClosed    : (m : f t) -> IsClosed (carrier m) (operation m)


-- |
-- The trivial magma type.
--
public export
record Magma (t : Type) where
    constructor MkMagma
    magma_carrier   : Set t
    magma_operation : t -> t -> t
    magma_isClosed  : IsClosed magma_carrier magma_operation

public export
IsMagma Magma where
    carrier     = magma_carrier
    operation   = magma_operation
    isClosed    = magma_isClosed

-- |
-- Anything which implements the 'IsMagma' interface can be
-- projected onto a trivial magma.
-- 
public export
toMagma : IsMagma f => f t -> Magma t
toMagma m = MkMagma (carrier m) (operation m) (isClosed m)
