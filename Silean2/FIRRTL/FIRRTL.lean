mutual

  structure PassiveItemType where
    name : String
    type : PassiveType

  inductive PassiveType where
    | uint (width : Nat)
    | sint (width : Nat)
    | pvector (length : Nat) (element : PassiveType)
    -- name, flip, type
    | pbundle (namesAndTypes : List PassiveItemType)
    | enum (namesAndTypes : List PassiveItemType)
end

mutual
  structure BundleItemType where
    name : String
    flip : Bool
    type : WType

  inductive WType where
    | p (passive : PassiveType)
    | vector (length : Nat) (element : WType)
    | bundle (namesAndTypes : List BundleItemType)
end

inductive TType where
  | w (wtype : WType)
  | const (wtype : WType)


inductive PType where
  | integer
  | string
  | bool
  | double

-- Types of circuit components

-- Node
-- Wire
-- Register
-- Output Port
-- Input Port
-- Submodule instances
-- Memories

-- An expression has a flow
-- nodes are sources
-- wires and registers are duplex
-- input ports are sources
-- output ports are duplex
-- memories are sources
inductive Flow where
  | source
  | sink
  | duplex

-- connect statement
-- the types of the two sides must be equivalent
-- the flow of the LHS must be sink or duplex
-- the (flow of the RHS must be source or duplex) or (RHS is of passtive type??)
-- neither side can be property types
-- It is ok if width of sint or uint goes from narrow to wide. they are sign extended.
-- Ordering of connects is significant. Later ones take precedence.
-- connection myoutput, myinput

structure ConnectionLHS where
  -- Is an expression I think
  -- The flow must be a sink or duplex
  -- Cannot be a property type
  temp : Nat

structure ConnectionRHS where
  -- The flow must be a source or duplex for a passive sink 
  temp : Nat

structure Connection where
  lhs : ConnectionLHS
  rhs : ConnectionRHS

structure Module where
  connections : List Connection

