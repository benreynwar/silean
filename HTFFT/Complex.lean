import Std

namespace HTFFT

/-! A deliberately small complex-number type used by both the exact and
fixed-point specifications. It is independent of any hardware representation. -/

structure Complex (α : Type) where
  real : α
  imag : α
  deriving Repr, DecidableEq

namespace Complex

def map (function : α → β) (value : Complex α) : Complex β :=
  { real := function value.real
    imag := function value.imag }

def add [Add α] (left right : Complex α) : Complex α :=
  { real := left.real + right.real
    imag := left.imag + right.imag }

def sub [Sub α] (left right : Complex α) : Complex α :=
  { real := left.real - right.real
    imag := left.imag - right.imag }

def mul [Mul α] [Add α] [Sub α] (left right : Complex α) : Complex α :=
  { real := left.real * right.real - left.imag * right.imag
    imag := left.real * right.imag + left.imag * right.real }

instance [Add α] : Add (Complex α) := ⟨add⟩
instance [Sub α] : Sub (Complex α) := ⟨sub⟩
instance [Mul α] [Add α] [Sub α] : Mul (Complex α) := ⟨mul⟩

@[simp] theorem map_real (function : α → β) (value : Complex α) :
    (value.map function).real = function value.real := rfl

@[simp] theorem map_imag (function : α → β) (value : Complex α) :
    (value.map function).imag = function value.imag := rfl

@[simp] theorem add_real [Add α] (left right : Complex α) :
    (left + right).real = left.real + right.real := rfl

@[simp] theorem add_imag [Add α] (left right : Complex α) :
    (left + right).imag = left.imag + right.imag := rfl

@[simp] theorem sub_real [Sub α] (left right : Complex α) :
    (left - right).real = left.real - right.real := rfl

@[simp] theorem sub_imag [Sub α] (left right : Complex α) :
    (left - right).imag = left.imag - right.imag := rfl

@[simp] theorem mul_real [Mul α] [Add α] [Sub α]
    (left right : Complex α) :
    (left * right).real =
      left.real * right.real - left.imag * right.imag := rfl

@[simp] theorem mul_imag [Mul α] [Add α] [Sub α]
    (left right : Complex α) :
    (left * right).imag =
      left.real * right.imag + left.imag * right.real := rfl

end Complex

end HTFFT
