import Silean.Authoring.SignalSchema
import Silean.Foundation.DeriveEnumeration

namespace Silean.Authoring

open Lean Elab Command
open Lean.Parser.Term

declare_syntax_cat signalSchemaParam
syntax "(" ident " : " term ")" : signalSchemaParam

declare_syntax_cat signalSchemaField
syntax ident " : " term : signalSchemaField

/-- Declare a reusable named-tuple schema. Field terms are themselves schemas,
so declarations compose naturally and may be parameterized. The declaration
generates `Field`, `signalMap`, `signalType`, `field`, and `schema`: typed field
labels, their labelled shapes, the aggregate shape, typed access to each field's
schema, and the aggregate naming tree. -/
syntax (name := signalSchema)
  "signal_schema " ident signalSchemaParam* " where "
    signalSchemaField,* : command

private structure SchemaParam where
  binder : TSyntax ``Parser.Term.bracketedBinder
  argument : TSyntax `term

private structure SchemaField where
  label : TSyntax `ident
  schema : TSyntax `term
deriving Inhabited

private def parseParam (parameter : TSyntax `signalSchemaParam) :
    CommandElabM SchemaParam :=
  match parameter with
  | `(signalSchemaParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def parseField (field : TSyntax `signalSchemaField) :
    CommandElabM SchemaField :=
  match field with
  | `(signalSchemaField| $label:ident : $schema:term) =>
      pure { label, schema }
  | _ => throwUnsupportedSyntax

private def namingFieldsTerm : List SchemaField → CommandElabM (TSyntax `term)
  | [] => `(Silean.Naming.SignalTypesNaming.nil)
  | field :: rest => do
      let sourceName := Syntax.mkStrLit field.label.getId.toString
      `(Silean.Naming.SignalTypesNaming.cons $sourceName
        $(field.schema) $(← namingFieldsTerm rest))

private def fieldConstructor (field : SchemaField) :
    CommandElabM (TSyntax ``Parser.Command.ctor) :=
  `(Parser.Command.ctor| | $(field.label):ident)

private def signalTypeAlternative (field : SchemaField) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  `(matchAltExpr| | .$(field.label):ident =>
    Silean.Authoring.SignalSchema.signalType $(field.schema))

private def fieldAlternative (field : SchemaField) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  `(matchAltExpr| | .$(field.label):ident => $(field.schema))

elab_rules : command
  | `(signal_schema $schemaName:ident $parameters:signalSchemaParam* where
      $fieldSyntax:signalSchemaField,*) => do
    let parsedParams ← parameters.mapM parseParam
    let binders := parsedParams.map (·.binder)
    let arguments := parsedParams.map (·.argument)
    let fields ← fieldSyntax.getElems.mapM parseField
    let labels := fields.map (·.label.getId)
    for reserved in [`Field, `signalMap, `signalType, `field, `schema] do
      if labels.contains reserved then
        throwErrorAt schemaName
          "a schema field cannot use the reserved name `{reserved}`"
    for index in [:labels.size] do
      for previous in [:index] do
        if labels[index]! == labels[previous]! then
          throwErrorAt fields[index]!.label
            "duplicate schema field `{fields[index]!.label.getId}`"
    let namingFieldsValue ← namingFieldsTerm fields.toList
    let constructors ← fields.mapM fieldConstructor
    let signalTypes ← fields.mapM signalTypeAlternative
    let fieldSchemas ← fields.mapM fieldAlternative
    let fieldName := mkIdentFrom schemaName `Field
    let signalTypeName := mkIdentFrom schemaName `signalType
    let fieldNameValue := mkIdentFrom schemaName `field
    let schemaValueName := mkIdentFrom schemaName `schema
    let signalMapName := mkIdentFrom schemaName `signalMap
    elabCommand <| ← `(namespace $schemaName)
    elabCommand <| ← `(
      inductive $fieldName where
        $constructors:ctor*
      deriving Silean.Enumeration
    )
    elabCommand <| ← `(
      @[reducible] def $signalMapName $binders:bracketedBinder* : Silean.SignalMap :=
        Silean.EnumeratedMap.of $fieldName fun $signalTypes:matchAlt*
    )
    elabCommand <| ← `(
      def $signalTypeName $binders:bracketedBinder* : Silean.SignalType :=
        ($signalMapName $arguments:term*).tupleType
    )
    elabCommand <| ← `(
      def $fieldNameValue $binders:bracketedBinder* :
          (field : ($signalMapName $arguments:term*).Label) →
            Silean.Authoring.SignalSchema
              (($signalMapName $arguments:term*).signalType field) :=
        fun $fieldSchemas:matchAlt*
    )
    elabCommand <| ← `(
      def $schemaValueName $binders:bracketedBinder* :
          Silean.Authoring.SignalSchema ($signalTypeName $arguments:term*) :=
        .tuple $namingFieldsValue
    )
    elabCommand <| ← `(end $schemaName)

end Silean.Authoring
