import Silean.Contracts.SignalExpectation
import Silean.Foundation.DeriveEnumeration

namespace SileanTests.SignalExpectation

open Silean

inductive Output
  | valid
  | payload
deriving Enumeration

abbrev PayloadFields : SignalTypes :=
  .cons (.vector 2 .bit) (.cons (.tuple (.cons .bit (.cons .bit .nil))) .nil)

def outputs : SignalMap := EnumeratedMap.of Output fun
  | .valid => .bit
  | .payload => .tuple PayloadFields

def actual : outputs.Values
  | .valid => true
  | .payload => (fun | 0 => false | 1 => true, ((false, (true, ())), ()))

def expected : outputs.Expectations
  | .valid => .one
  | .payload =>
      (fun | 0 => .dontCare | 1 => .one,
        ((.zero, (.dontCare, ())), ()))

example : outputs.Matches expected actual := by
  intro output
  cases output <;> simp [outputs, PayloadFields, expected, actual,
    SignalType.Matches, SignalTypes.Matches, BitExpectation.Matches]

example : outputs.Matches outputs.dontCareExpectations actual := by simp

example : outputs.Matches (outputs.exactExpectations actual) actual := by simp

def different : outputs.Values
  | .valid => false
  | .payload => actual .payload

example : ¬outputs.Matches (outputs.exactExpectations actual) different := by
  rw [SignalMap.exactExpectations_match_iff]
  intro equal
  have := congrFun equal Output.valid
  simp [actual, different] at this

end SileanTests.SignalExpectation
