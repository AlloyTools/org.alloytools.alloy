module tests/test -- This model is contributed by Nicolas Rouquette from JPL

abstract sig h_Element {
       hierarchy : set h_Element,
       degree : one Int
}

abstract sig h_AbstractElement, h_ConcreteElement extends h_Element {}

one sig h_Polymorphism {
       context : set h_Element,
       roots : set h_Element
}{
       all e:h_Element {
               not (e.degree = 1) <=> e in context
               no e.hierarchy <=> e in roots
}}

one sig Comment extends h_ConcreteElement {}
one sig DirectedRelationship extends h_AbstractElement {}
one sig LiteralSpecification extends h_AbstractElement {}
one sig LiteralInteger extends h_ConcreteElement {}
one sig LiteralString extends h_ConcreteElement {}
one sig LiteralBoolean extends h_ConcreteElement {}
one sig LiteralNull extends h_ConcreteElement {}
one sig Constraint extends h_ConcreteElement {}
one sig ElementImport extends h_ConcreteElement {}
one sig TypedElement extends h_AbstractElement {}
one sig Feature extends h_AbstractElement {}
one sig RedefinableElement extends h_AbstractElement {}
one sig StructuralFeature extends h_AbstractElement {}
one sig Slot extends h_ConcreteElement {}
one sig PackageImport extends h_ConcreteElement {}
one sig DataType extends h_ConcreteElement {}
one sig Enumeration extends h_ConcreteElement {}
one sig EnumerationLiteral extends h_ConcreteElement {}
one sig PrimitiveType extends h_ConcreteElement {}
one sig Association extends h_ConcreteElement {}
one sig Relationship extends h_AbstractElement {}
one sig PackageMerge extends h_ConcreteElement {}
one sig InstanceValue extends h_ConcreteElement {}
one sig LiteralUnlimitedNatural extends h_ConcreteElement {}
one sig Type extends h_AbstractElement {}
one sig Expression extends h_ConcreteElement {}
one sig OpaqueExpression extends h_ConcreteElement {}
one sig OpaqueBehavior extends h_ConcreteElement {}
one sig FunctionBehavior extends h_ConcreteElement {}
one sig OpaqueAction extends h_ConcreteElement {}
one sig CallAction extends h_AbstractElement {}
one sig SendSignalAction extends h_ConcreteElement {}
one sig CallOperationAction extends h_ConcreteElement {}
one sig CallBehaviorAction extends h_ConcreteElement {}
one sig MultiplicityElement extends h_AbstractElement {}
one sig SequenceNode extends h_ConcreteElement {}
one sig InputPin extends h_ConcreteElement {}
one sig OutputPin extends h_ConcreteElement {}
one sig Usage extends h_ConcreteElement {}
one sig Abstraction extends h_ConcreteElement {}
one sig Dependency extends h_ConcreteElement {}
one sig Realization extends h_ConcreteElement {}
one sig Substitution extends h_ConcreteElement {}
one sig Namespace extends h_AbstractElement {}
one sig InterfaceRealization extends h_ConcreteElement {}
one sig StructuredClassifier extends h_AbstractElement {}
one sig Variable extends h_ConcreteElement {}
one sig CollaborationUse extends h_ConcreteElement {}
one sig Collaboration extends h_ConcreteElement {}
one sig ControlNode extends h_AbstractElement {}
one sig ControlFlow extends h_ConcreteElement {}
one sig InitialNode extends h_ConcreteElement {}
one sig ActivityParameterNode extends h_ConcreteElement {}
one sig ValuePin extends h_ConcreteElement {}
one sig Message extends h_ConcreteElement {}
one sig GeneralOrdering extends h_ConcreteElement {}
one sig ExecutionSpecification extends h_AbstractElement {}
one sig OccurrenceSpecification extends h_ConcreteElement {}
one sig MessageEnd extends h_AbstractElement {}
one sig StateInvariant extends h_ConcreteElement {}
one sig ActionExecutionSpecification extends h_ConcreteElement {}
one sig BehaviorExecutionSpecification extends h_ConcreteElement {}
one sig ExecutionEvent extends h_ConcreteElement {}
one sig CreationEvent extends h_ConcreteElement {}
one sig DestructionEvent extends h_ConcreteElement {}
one sig SendOperationEvent extends h_ConcreteElement {}
one sig SendSignalEvent extends h_ConcreteElement {}
one sig MessageOccurrenceSpecification extends h_ConcreteElement {}
one sig ExecutionOccurrenceSpecification extends h_ConcreteElement {}
one sig ReceiveOperationEvent extends h_ConcreteElement {}
one sig ReceiveSignalEvent extends h_ConcreteElement {}
one sig Actor extends h_ConcreteElement {}
one sig Extend extends h_ConcreteElement {}
one sig Include extends h_ConcreteElement {}
one sig UseCase extends h_ConcreteElement {}
one sig ExtensionPoint extends h_ConcreteElement {}
one sig CallEvent extends h_ConcreteElement {}
one sig ChangeEvent extends h_ConcreteElement {}
one sig Reception extends h_ConcreteElement {}
one sig Signal extends h_ConcreteElement {}
one sig SignalEvent extends h_ConcreteElement {}
one sig MessageEvent extends h_AbstractElement {}
one sig AnyReceiveEvent extends h_ConcreteElement {}
one sig BehavioredClassifier extends h_AbstractElement {}
one sig Event extends h_AbstractElement {}
one sig ForkNode extends h_ConcreteElement {}
one sig FlowFinalNode extends h_ConcreteElement {}
one sig CentralBufferNode extends h_ConcreteElement {}
one sig ActivityPartition extends h_ConcreteElement {}
one sig MergeNode extends h_ConcreteElement {}
one sig DecisionNode extends h_ConcreteElement {}
one sig FinalNode extends h_AbstractElement {}
one sig ActivityFinalNode extends h_ConcreteElement {}
one sig EncapsulatedClassifier extends h_AbstractElement {}
one sig ConnectorEnd extends h_ConcreteElement {}
one sig ComponentRealization extends h_ConcreteElement {}
one sig Connector extends h_ConcreteElement {}
one sig Manifestation extends h_ConcreteElement {}
one sig Node extends h_ConcreteElement {}
one sig Device extends h_ConcreteElement {}
one sig ExecutionEnvironment extends h_ConcreteElement {}
one sig DeploymentTarget extends h_AbstractElement {}
one sig DeployedArtifact extends h_AbstractElement {}
one sig CommunicationPath extends h_ConcreteElement {}
one sig InstanceSpecification extends h_ConcreteElement {}
one sig Artifact extends h_ConcreteElement {}
one sig InteractionUse extends h_ConcreteElement {}
one sig PartDecomposition extends h_ConcreteElement {}
one sig InteractionOperand extends h_ConcreteElement {}
one sig InteractionConstraint extends h_ConcreteElement {}
one sig Gate extends h_ConcreteElement {}
one sig CombinedFragment extends h_ConcreteElement {}
one sig Interaction extends h_ConcreteElement {}
one sig Lifeline extends h_ConcreteElement {}
one sig Continuation extends h_ConcreteElement {}
one sig InteractionFragment extends h_AbstractElement {}
one sig ConsiderIgnoreFragment extends h_ConcreteElement {}
one sig CreateObjectAction extends h_ConcreteElement {}
one sig DestroyObjectAction extends h_ConcreteElement {}
one sig TestIdentityAction extends h_ConcreteElement {}
one sig ReadSelfAction extends h_ConcreteElement {}
one sig StructuralFeatureAction extends h_AbstractElement {}
one sig ReadStructuralFeatureAction extends h_ConcreteElement {}
one sig WriteStructuralFeatureAction extends h_AbstractElement {}
one sig ClearStructuralFeatureAction extends h_ConcreteElement {}
one sig RemoveStructuralFeatureValueAction extends h_ConcreteElement {}
one sig AddStructuralFeatureValueAction extends h_ConcreteElement {}
one sig LinkAction extends h_AbstractElement {}
one sig ReadLinkAction extends h_ConcreteElement {}
one sig LinkEndCreationData extends h_ConcreteElement {}
one sig CreateLinkAction extends h_ConcreteElement {}
one sig DestroyLinkAction extends h_ConcreteElement {}
one sig WriteLinkAction extends h_AbstractElement {}
one sig ClearAssociationAction extends h_ConcreteElement {}
one sig BroadcastSignalAction extends h_ConcreteElement {}
one sig SendObjectAction extends h_ConcreteElement {}
one sig LinkEndDestructionData extends h_ConcreteElement {}
one sig ValueSpecificationAction extends h_ConcreteElement {}
one sig TimeExpression extends h_ConcreteElement {}
one sig Duration extends h_ConcreteElement {}
one sig DurationInterval extends h_ConcreteElement {}
one sig TimeConstraint extends h_ConcreteElement {}
one sig TimeInterval extends h_ConcreteElement {}
one sig DurationConstraint extends h_ConcreteElement {}
one sig IntervalConstraint extends h_ConcreteElement {}
one sig Interval extends h_ConcreteElement {}
one sig Observation extends h_AbstractElement {}
one sig TimeObservation extends h_ConcreteElement {}
one sig DurationObservation extends h_ConcreteElement {}
one sig InvocationAction extends h_AbstractElement {}
one sig Trigger extends h_ConcreteElement {}
one sig StateMachine extends h_ConcreteElement {}
one sig Transition extends h_ConcreteElement {}
one sig Vertex extends h_AbstractElement {}
one sig Pseudostate extends h_ConcreteElement {}
one sig FinalState extends h_ConcreteElement {}
one sig ConnectionPointReference extends h_ConcreteElement {}
one sig TimeEvent extends h_ConcreteElement {}
one sig Stereotype extends h_ConcreteElement {}
one sig Profile extends h_ConcreteElement {}
one sig Class extends h_ConcreteElement {}
one sig ProfileApplication extends h_ConcreteElement {}
one sig Extension extends h_ConcreteElement {}
one sig Image extends h_ConcreteElement {}
one sig Element extends h_AbstractElement {}
one sig ExtensionEnd extends h_ConcreteElement {}
one sig VariableAction extends h_AbstractElement {}
one sig ReadVariableAction extends h_ConcreteElement {}
one sig WriteVariableAction extends h_AbstractElement {}
one sig ClearVariableAction extends h_ConcreteElement {}
one sig AddVariableValueAction extends h_ConcreteElement {}
one sig RemoveVariableValueAction extends h_ConcreteElement {}
one sig RaiseExceptionAction extends h_ConcreteElement {}
one sig ActionInputPin extends h_ConcreteElement {}
one sig GeneralizationSet extends h_ConcreteElement {}
one sig Generalization extends h_ConcreteElement {}
one sig InformationItem extends h_ConcreteElement {}
one sig InformationFlow extends h_ConcreteElement {}
one sig Model extends h_ConcreteElement {}
one sig ReadExtentAction extends h_ConcreteElement {}
one sig ReclassifyObjectAction extends h_ConcreteElement {}
one sig ReadIsClassifiedObjectAction extends h_ConcreteElement {}
one sig StartClassifierBehaviorAction extends h_ConcreteElement {}
one sig QualifierValue extends h_ConcreteElement {}
one sig LinkEndData extends h_ConcreteElement {}
one sig ReadLinkObjectEndAction extends h_ConcreteElement {}
one sig ReadLinkObjectEndQualifierAction extends h_ConcreteElement {}
one sig CreateLinkObjectAction extends h_ConcreteElement {}
one sig AcceptEventAction extends h_ConcreteElement {}
one sig AcceptCallAction extends h_ConcreteElement {}
one sig ReplyAction extends h_ConcreteElement {}
one sig UnmarshallAction extends h_ConcreteElement {}
one sig ReduceAction extends h_ConcreteElement {}
one sig JoinNode extends h_ConcreteElement {}
one sig DataStoreNode extends h_ConcreteElement {}
one sig ObjectFlow extends h_ConcreteElement {}
one sig ObjectNode extends h_AbstractElement {}
one sig ParameterSet extends h_ConcreteElement {}
one sig Activity extends h_ConcreteElement {}
one sig Parameter extends h_ConcreteElement {}
one sig Action extends h_AbstractElement {}
one sig InterruptibleActivityRegion extends h_ConcreteElement {}
one sig ActivityNode extends h_AbstractElement {}
one sig BehavioralFeature extends h_AbstractElement {}
one sig Behavior extends h_AbstractElement {}
one sig Pin extends h_ConcreteElement {}
one sig ConditionalNode extends h_ConcreteElement {}
one sig StructuredActivityNode extends h_ConcreteElement {}
one sig LoopNode extends h_ConcreteElement {}
one sig Clause extends h_ConcreteElement {}
one sig ActivityEdge extends h_AbstractElement {}
one sig ActivityGroup extends h_AbstractElement {}
one sig ExpansionNode extends h_ConcreteElement {}
one sig ExpansionRegion extends h_ConcreteElement {}
one sig ExecutableNode extends h_AbstractElement {}
one sig ExceptionHandler extends h_ConcreteElement {}
one sig Component extends h_ConcreteElement {}
one sig Deployment extends h_ConcreteElement {}
one sig DeploymentSpecification extends h_ConcreteElement {}
one sig ProtocolConformance extends h_ConcreteElement {}
one sig Interface extends h_ConcreteElement {}
one sig Port extends h_ConcreteElement {}
one sig ProtocolTransition extends h_ConcreteElement {}
one sig ProtocolStateMachine extends h_ConcreteElement {}
one sig State extends h_ConcreteElement {}
one sig Region extends h_ConcreteElement {}
one sig AssociationClass extends h_ConcreteElement {}
one sig TemplateSignature extends h_ConcreteElement {}
one sig NamedElement extends h_AbstractElement {}
one sig TemplateParameter extends h_ConcreteElement {}
one sig StringExpression extends h_ConcreteElement {}
one sig TemplateBinding extends h_ConcreteElement {}
one sig TemplateParameterSubstitution extends h_ConcreteElement {}
one sig TemplateableElement extends h_AbstractElement {}
one sig ParameterableElement extends h_AbstractElement {}
one sig Property extends h_ConcreteElement {}
one sig ValueSpecification extends h_AbstractElement {}
one sig Operation extends h_ConcreteElement {}
one sig OperationTemplateParameter extends h_ConcreteElement {}
one sig PackageableElement extends h_AbstractElement {}
one sig Classifier extends h_AbstractElement {}
one sig ClassifierTemplateParameter extends h_ConcreteElement {}
one sig RedefinableTemplateSignature extends h_ConcreteElement {}
one sig ConnectableElement extends h_AbstractElement {}
one sig ConnectableElementTemplateParameter extends h_ConcreteElement {}
one sig Package extends h_ConcreteElement {}
fact {
 hierarchy = (this/Comment -> this/Element)
 + (this/DirectedRelationship -> this/Relationship)
 + (this/LiteralSpecification -> this/ValueSpecification)
 + (this/LiteralInteger -> this/LiteralSpecification)
 + (this/LiteralString -> this/LiteralSpecification)
 + (this/LiteralBoolean -> this/LiteralSpecification)
 + (this/LiteralNull -> this/LiteralSpecification)
 + (this/Constraint -> this/PackageableElement)
 + (this/ElementImport -> this/DirectedRelationship)
 + (this/TypedElement -> this/NamedElement)
 + (this/Feature -> this/RedefinableElement)
 + (this/RedefinableElement -> this/NamedElement)
 + (this/StructuralFeature -> this/Feature)
 + (this/StructuralFeature -> this/TypedElement)
 + (this/StructuralFeature -> this/MultiplicityElement)
 + (this/Slot -> this/Element)
 + (this/PackageImport -> this/DirectedRelationship)
 + (this/DataType -> this/Classifier)
 + (this/Enumeration -> this/DataType)
 + (this/EnumerationLiteral -> this/InstanceSpecification)
 + (this/PrimitiveType -> this/DataType)
 + (this/Association -> this/Relationship)
 + (this/Association -> this/Classifier)
 + (this/Relationship -> this/Element)
 + (this/PackageMerge -> this/DirectedRelationship)
 + (this/InstanceValue -> this/ValueSpecification)
 + (this/LiteralUnlimitedNatural -> this/LiteralSpecification)
 + (this/Type -> this/PackageableElement)
 + (this/Expression -> this/ValueSpecification)
 + (this/OpaqueExpression -> this/ValueSpecification)
 + (this/OpaqueBehavior -> this/Behavior)
 + (this/FunctionBehavior -> this/OpaqueBehavior)
 + (this/OpaqueAction -> this/Action)
 + (this/CallAction -> this/InvocationAction)
 + (this/SendSignalAction -> this/InvocationAction)
 + (this/CallOperationAction -> this/CallAction)
 + (this/CallBehaviorAction -> this/CallAction)
 + (this/MultiplicityElement -> this/Element)
 + (this/SequenceNode -> this/StructuredActivityNode)
 + (this/InputPin -> this/Pin)
 + (this/OutputPin -> this/Pin)
 + (this/Usage -> this/Dependency)
 + (this/Abstraction -> this/Dependency)
 + (this/Dependency -> this/DirectedRelationship)
 + (this/Dependency -> this/PackageableElement)
 + (this/Realization -> this/Abstraction)
 + (this/Substitution -> this/Realization)
 + (this/Namespace -> this/NamedElement)
 + (this/InterfaceRealization -> this/Realization)
 + (this/StructuredClassifier -> this/Classifier)
 + (this/Variable -> this/MultiplicityElement)
 + (this/Variable -> this/ConnectableElement)
 + (this/CollaborationUse -> this/NamedElement)
 + (this/Collaboration -> this/StructuredClassifier)
 + (this/Collaboration -> this/BehavioredClassifier)
 + (this/ControlNode -> this/ActivityNode)
 + (this/ControlFlow -> this/ActivityEdge)
 + (this/InitialNode -> this/ControlNode)
 + (this/ActivityParameterNode -> this/ObjectNode)
 + (this/ValuePin -> this/InputPin)
 + (this/Message -> this/NamedElement)
 + (this/GeneralOrdering -> this/NamedElement)
 + (this/ExecutionSpecification -> this/InteractionFragment)
 + (this/OccurrenceSpecification -> this/InteractionFragment)
 + (this/MessageEnd -> this/NamedElement)
 + (this/StateInvariant -> this/InteractionFragment)
 + (this/ActionExecutionSpecification -> this/ExecutionSpecification)
 + (this/BehaviorExecutionSpecification -> this/ExecutionSpecification)
 + (this/ExecutionEvent -> this/Event)
 + (this/CreationEvent -> this/Event)
 + (this/DestructionEvent -> this/Event)
 + (this/SendOperationEvent -> this/MessageEvent)
 + (this/SendSignalEvent -> this/MessageEvent)
 + (this/MessageOccurrenceSpecification -> this/MessageEnd)
 + (this/MessageOccurrenceSpecification -> this/OccurrenceSpecification)
 + (this/ExecutionOccurrenceSpecification -> this/OccurrenceSpecification)
 + (this/ReceiveOperationEvent -> this/MessageEvent)
 + (this/ReceiveSignalEvent -> this/MessageEvent)
 + (this/Actor -> this/BehavioredClassifier)
 + (this/Extend -> this/DirectedRelationship)
 + (this/Extend -> this/NamedElement)
 + (this/Include -> this/DirectedRelationship)
 + (this/Include -> this/NamedElement)
 + (this/UseCase -> this/BehavioredClassifier)
 + (this/ExtensionPoint -> this/RedefinableElement)
 + (this/CallEvent -> this/MessageEvent)
 + (this/ChangeEvent -> this/Event)
 + (this/Reception -> this/BehavioralFeature)
 + (this/Signal -> this/Classifier)
 + (this/SignalEvent -> this/MessageEvent)
 + (this/MessageEvent -> this/Event)
 + (this/AnyReceiveEvent -> this/MessageEvent)
 + (this/BehavioredClassifier -> this/Classifier)
 + (this/Event -> this/PackageableElement)
 + (this/ForkNode -> this/ControlNode)
 + (this/FlowFinalNode -> this/FinalNode)
 + (this/CentralBufferNode -> this/ObjectNode)
 + (this/ActivityPartition -> this/NamedElement)
 + (this/ActivityPartition -> this/ActivityGroup)
 + (this/MergeNode -> this/ControlNode)
 + (this/DecisionNode -> this/ControlNode)
 + (this/FinalNode -> this/ControlNode)
 + (this/ActivityFinalNode -> this/FinalNode)
 + (this/EncapsulatedClassifier -> this/StructuredClassifier)
 + (this/ConnectorEnd -> this/MultiplicityElement)
 + (this/ComponentRealization -> this/Realization)
 + (this/Connector -> this/Feature)
 + (this/Manifestation -> this/Abstraction)
 + (this/Node -> this/Class)
 + (this/Node -> this/DeploymentTarget)
 + (this/Device -> this/Node)
 + (this/ExecutionEnvironment -> this/Node)
 + (this/DeploymentTarget -> this/NamedElement)
 + (this/DeployedArtifact -> this/NamedElement)
 + (this/CommunicationPath -> this/Association)
 + (this/InstanceSpecification -> this/PackageableElement)
 + (this/InstanceSpecification -> this/DeploymentTarget)
 + (this/InstanceSpecification -> this/DeployedArtifact)
 + (this/Artifact -> this/Classifier)
 + (this/Artifact -> this/DeployedArtifact)
 + (this/InteractionUse -> this/InteractionFragment)
 + (this/PartDecomposition -> this/InteractionUse)
 + (this/InteractionOperand -> this/InteractionFragment)
 + (this/InteractionOperand -> this/Namespace)
 + (this/InteractionConstraint -> this/Constraint)
 + (this/Gate -> this/MessageEnd)
 + (this/CombinedFragment -> this/InteractionFragment)
 + (this/Interaction -> this/InteractionFragment)
 + (this/Interaction -> this/Behavior)
 + (this/Lifeline -> this/NamedElement)
 + (this/Continuation -> this/InteractionFragment)
 + (this/InteractionFragment -> this/NamedElement)
 + (this/ConsiderIgnoreFragment -> this/CombinedFragment)
 + (this/CreateObjectAction -> this/Action)
 + (this/DestroyObjectAction -> this/Action)
 + (this/TestIdentityAction -> this/Action)
 + (this/ReadSelfAction -> this/Action)
 + (this/StructuralFeatureAction -> this/Action)
 + (this/ReadStructuralFeatureAction -> this/StructuralFeatureAction)
 + (this/WriteStructuralFeatureAction -> this/StructuralFeatureAction)
 + (this/ClearStructuralFeatureAction -> this/StructuralFeatureAction)
 + (this/RemoveStructuralFeatureValueAction -> this/WriteStructuralFeatureAction)
 + (this/AddStructuralFeatureValueAction -> this/WriteStructuralFeatureAction)
 + (this/LinkAction -> this/Action)
 + (this/ReadLinkAction -> this/LinkAction)
 + (this/LinkEndCreationData -> this/LinkEndData)
 + (this/CreateLinkAction -> this/WriteLinkAction)
 + (this/DestroyLinkAction -> this/WriteLinkAction)
 + (this/WriteLinkAction -> this/LinkAction)
 + (this/ClearAssociationAction -> this/Action)
 + (this/BroadcastSignalAction -> this/InvocationAction)
 + (this/SendObjectAction -> this/InvocationAction)
 + (this/LinkEndDestructionData -> this/LinkEndData)
 + (this/ValueSpecificationAction -> this/Action)
 + (this/TimeExpression -> this/ValueSpecification)
 + (this/Duration -> this/ValueSpecification)
 + (this/DurationInterval -> this/Interval)
 + (this/TimeConstraint -> this/IntervalConstraint)
 + (this/TimeInterval -> this/Interval)
 + (this/DurationConstraint -> this/IntervalConstraint)
 + (this/IntervalConstraint -> this/Constraint)
 + (this/Interval -> this/ValueSpecification)
 + (this/Observation -> this/PackageableElement)
 + (this/TimeObservation -> this/Observation)
 + (this/DurationObservation -> this/Observation)
 + (this/InvocationAction -> this/Action)
 + (this/Trigger -> this/NamedElement)
 + (this/StateMachine -> this/Behavior)
 + (this/Transition -> this/RedefinableElement)
 + (this/Transition -> this/Namespace)
 + (this/Vertex -> this/NamedElement)
 + (this/Pseudostate -> this/Vertex)
 + (this/FinalState -> this/State)
 + (this/ConnectionPointReference -> this/Vertex)
 + (this/TimeEvent -> this/Event)
 + (this/Stereotype -> this/Class)
 + (this/Profile -> this/Package)
 + (this/Class -> this/BehavioredClassifier)
 + (this/Class -> this/EncapsulatedClassifier)
 + (this/ProfileApplication -> this/DirectedRelationship)
 + (this/Extension -> this/Association)
 + (this/Image -> this/Element)
 + (this/ExtensionEnd -> this/Property)
 + (this/VariableAction -> this/Action)
 + (this/ReadVariableAction -> this/VariableAction)
 + (this/WriteVariableAction -> this/VariableAction)
 + (this/ClearVariableAction -> this/VariableAction)
 + (this/AddVariableValueAction -> this/WriteVariableAction)
 + (this/RemoveVariableValueAction -> this/WriteVariableAction)
 + (this/RaiseExceptionAction -> this/Action)
 + (this/ActionInputPin -> this/InputPin)
 + (this/GeneralizationSet -> this/PackageableElement)
 + (this/Generalization -> this/DirectedRelationship)
 + (this/InformationItem -> this/Classifier)
 + (this/InformationFlow -> this/DirectedRelationship)
 + (this/InformationFlow -> this/PackageableElement)
 + (this/Model -> this/Package)
 + (this/ReadExtentAction -> this/Action)
 + (this/ReclassifyObjectAction -> this/Action)
 + (this/ReadIsClassifiedObjectAction -> this/Action)
 + (this/StartClassifierBehaviorAction -> this/Action)
 + (this/QualifierValue -> this/Element)
 + (this/LinkEndData -> this/Element)
 + (this/ReadLinkObjectEndAction -> this/Action)
 + (this/ReadLinkObjectEndQualifierAction -> this/Action)
 + (this/CreateLinkObjectAction -> this/CreateLinkAction)
 + (this/AcceptEventAction -> this/Action)
 + (this/AcceptCallAction -> this/AcceptEventAction)
 + (this/ReplyAction -> this/Action)
 + (this/UnmarshallAction -> this/Action)
 + (this/ReduceAction -> this/Action)
 + (this/JoinNode -> this/ControlNode)
 + (this/DataStoreNode -> this/CentralBufferNode)
 + (this/ObjectFlow -> this/ActivityEdge)
 + (this/ObjectNode -> this/ActivityNode)
 + (this/ObjectNode -> this/TypedElement)
 + (this/ParameterSet -> this/NamedElement)
 + (this/Activity -> this/Behavior)
 + (this/Parameter -> this/MultiplicityElement)
 + (this/Parameter -> this/ConnectableElement)
 + (this/Action -> this/ExecutableNode)
 + (this/InterruptibleActivityRegion -> this/ActivityGroup)
 + (this/ActivityNode -> this/RedefinableElement)
 + (this/BehavioralFeature -> this/Feature)
 + (this/BehavioralFeature -> this/Namespace)
 + (this/Behavior -> this/Class)
 + (this/Pin -> this/MultiplicityElement)
 + (this/Pin -> this/ObjectNode)
 + (this/ConditionalNode -> this/StructuredActivityNode)
 + (this/StructuredActivityNode -> this/Namespace)
 + (this/StructuredActivityNode -> this/Action)
 + (this/StructuredActivityNode -> this/ActivityGroup)
 + (this/LoopNode -> this/StructuredActivityNode)
 + (this/Clause -> this/Element)
 + (this/ActivityEdge -> this/RedefinableElement)
 + (this/ActivityGroup -> this/Element)
 + (this/ExpansionNode -> this/ObjectNode)
 + (this/ExpansionRegion -> this/StructuredActivityNode)
 + (this/ExecutableNode -> this/ActivityNode)
 + (this/ExceptionHandler -> this/Element)
 + (this/Component -> this/Class)
 + (this/Component -> this/Namespace)
 + (this/Deployment -> this/Dependency)
 + (this/DeploymentSpecification -> this/Artifact)
 + (this/ProtocolConformance -> this/DirectedRelationship)
 + (this/Interface -> this/Classifier)
 + (this/Port -> this/Property)
 + (this/ProtocolTransition -> this/Transition)
 + (this/ProtocolStateMachine -> this/StateMachine)
 + (this/State -> this/Vertex)
 + (this/State -> this/RedefinableElement)
 + (this/State -> this/Namespace)
 + (this/Region -> this/RedefinableElement)
 + (this/Region -> this/Namespace)
 + (this/AssociationClass -> this/Association)
 + (this/AssociationClass -> this/Class)
 + (this/TemplateSignature -> this/Element)
 + (this/NamedElement -> this/Element)
 + (this/TemplateParameter -> this/Element)
 + (this/StringExpression -> this/TemplateableElement)
 + (this/StringExpression -> this/Expression)
 + (this/TemplateBinding -> this/DirectedRelationship)
 + (this/TemplateParameterSubstitution -> this/Element)
 + (this/TemplateableElement -> this/Element)
 + (this/ParameterableElement -> this/Element)
 + (this/Property -> this/ConnectableElement)
 + (this/Property -> this/DeploymentTarget)
 + (this/Property -> this/StructuralFeature)
 + (this/Property -> this/TemplateableElement)
 + (this/ValueSpecification -> this/TypedElement)
 + (this/ValueSpecification -> this/PackageableElement)
 + (this/Operation -> this/BehavioralFeature)
 + (this/Operation -> this/ParameterableElement)
 + (this/Operation -> this/TemplateableElement)
 + (this/OperationTemplateParameter -> this/TemplateParameter)
 + (this/PackageableElement -> this/NamedElement)
 + (this/PackageableElement -> this/ParameterableElement)
 + (this/Classifier -> this/RedefinableElement)
 + (this/Classifier -> this/Type)
 + (this/Classifier -> this/TemplateableElement)
 + (this/Classifier -> this/Namespace)
 + (this/ClassifierTemplateParameter -> this/TemplateParameter)
 + (this/RedefinableTemplateSignature -> this/RedefinableElement)
 + (this/RedefinableTemplateSignature -> this/TemplateSignature)
 + (this/ConnectableElement -> this/TypedElement)
 + (this/ConnectableElement -> this/ParameterableElement)
 + (this/ConnectableElementTemplateParameter -> this/TemplateParameter)
 + (this/Package -> this/PackageableElement)
 + (this/Package -> this/Namespace)
 + (this/Package -> this/TemplateableElement)
 degree = (this/Comment -> 1)
 + (this/DirectedRelationship -> 1)
 + (this/LiteralSpecification -> 1)
 + (this/LiteralInteger -> 1)
 + (this/LiteralString -> 1)
 + (this/LiteralBoolean -> 1)
 + (this/LiteralNull -> 1)
 + (this/Constraint -> 1)
 + (this/ElementImport -> 1)
 + (this/TypedElement -> 1)
 + (this/Feature -> 1)
 + (this/RedefinableElement -> 1)
 + (this/StructuralFeature -> 3)
 + (this/Slot -> 1)
 + (this/PackageImport -> 1)
 + (this/DataType -> 1)
 + (this/Enumeration -> 1)
 + (this/EnumerationLiteral -> 1)
 + (this/PrimitiveType -> 1)
 + (this/Association -> 2)
 + (this/Relationship -> 1)
 + (this/PackageMerge -> 1)
 + (this/InstanceValue -> 1)
 + (this/LiteralUnlimitedNatural -> 1)
 + (this/Type -> 1)
 + (this/Expression -> 1)
 + (this/OpaqueExpression -> 1)
 + (this/OpaqueBehavior -> 1)
 + (this/FunctionBehavior -> 1)
 + (this/OpaqueAction -> 1)
 + (this/CallAction -> 1)
 + (this/SendSignalAction -> 1)
 + (this/CallOperationAction -> 1)
 + (this/CallBehaviorAction -> 1)
 + (this/MultiplicityElement -> 1)
 + (this/SequenceNode -> 1)
 + (this/InputPin -> 1)
 + (this/OutputPin -> 1)
 + (this/Usage -> 1)
 + (this/Abstraction -> 1)
 + (this/Dependency -> 2)
 + (this/Realization -> 1)
 + (this/Substitution -> 1)
 + (this/Namespace -> 1)
 + (this/InterfaceRealization -> 1)
 + (this/StructuredClassifier -> 1)
 + (this/Variable -> 2)
 + (this/CollaborationUse -> 1)
 + (this/Collaboration -> 2)
 + (this/ControlNode -> 1)
 + (this/ControlFlow -> 1)
 + (this/InitialNode -> 1)
 + (this/ActivityParameterNode -> 1)
 + (this/ValuePin -> 1)
 + (this/Message -> 1)
 + (this/GeneralOrdering -> 1)
 + (this/ExecutionSpecification -> 1)
 + (this/OccurrenceSpecification -> 1)
 + (this/MessageEnd -> 1)
 + (this/StateInvariant -> 1)
 + (this/ActionExecutionSpecification -> 1)
 + (this/BehaviorExecutionSpecification -> 1)
 + (this/ExecutionEvent -> 1)
 + (this/CreationEvent -> 1)
 + (this/DestructionEvent -> 1)
 + (this/SendOperationEvent -> 1)
 + (this/SendSignalEvent -> 1)
 + (this/MessageOccurrenceSpecification -> 2)
 + (this/ExecutionOccurrenceSpecification -> 1)
 + (this/ReceiveOperationEvent -> 1)
 + (this/ReceiveSignalEvent -> 1)
 + (this/Actor -> 1)
 + (this/Extend -> 2)
 + (this/Include -> 2)
 + (this/UseCase -> 1)
 + (this/ExtensionPoint -> 1)
 + (this/CallEvent -> 1)
 + (this/ChangeEvent -> 1)
 + (this/Reception -> 1)
 + (this/Signal -> 1)
 + (this/SignalEvent -> 1)
 + (this/MessageEvent -> 1)
 + (this/AnyReceiveEvent -> 1)
 + (this/BehavioredClassifier -> 1)
 + (this/Event -> 1)
 + (this/ForkNode -> 1)
 + (this/FlowFinalNode -> 1)
 + (this/CentralBufferNode -> 1)
 + (this/ActivityPartition -> 2)
 + (this/MergeNode -> 1)
 + (this/DecisionNode -> 1)
 + (this/FinalNode -> 1)
 + (this/ActivityFinalNode -> 1)
 + (this/EncapsulatedClassifier -> 1)
 + (this/ConnectorEnd -> 1)
 + (this/ComponentRealization -> 1)
 + (this/Connector -> 1)
 + (this/Manifestation -> 1)
 + (this/Node -> 2)
 + (this/Device -> 1)
 + (this/ExecutionEnvironment -> 1)
 + (this/DeploymentTarget -> 1)
 + (this/DeployedArtifact -> 1)
 + (this/CommunicationPath -> 1)
 + (this/InstanceSpecification -> 3)
 + (this/Artifact -> 2)
 + (this/InteractionUse -> 1)
 + (this/PartDecomposition -> 1)
 + (this/InteractionOperand -> 2)
 + (this/InteractionConstraint -> 1)
 + (this/Gate -> 1)
 + (this/CombinedFragment -> 1)
 + (this/Interaction -> 2)
 + (this/Lifeline -> 1)
 + (this/Continuation -> 1)
 + (this/InteractionFragment -> 1)
 + (this/ConsiderIgnoreFragment -> 1)
 + (this/CreateObjectAction -> 1)
 + (this/DestroyObjectAction -> 1)
 + (this/TestIdentityAction -> 1)
 + (this/ReadSelfAction -> 1)
 + (this/StructuralFeatureAction -> 1)
 + (this/ReadStructuralFeatureAction -> 1)
 + (this/WriteStructuralFeatureAction -> 1)
 + (this/ClearStructuralFeatureAction -> 1)
 + (this/RemoveStructuralFeatureValueAction -> 1)
 + (this/AddStructuralFeatureValueAction -> 1)
 + (this/LinkAction -> 1)
 + (this/ReadLinkAction -> 1)
 + (this/LinkEndCreationData -> 1)
 + (this/CreateLinkAction -> 1)
 + (this/DestroyLinkAction -> 1)
 + (this/WriteLinkAction -> 1)
 + (this/ClearAssociationAction -> 1)
 + (this/BroadcastSignalAction -> 1)
 + (this/SendObjectAction -> 1)
 + (this/LinkEndDestructionData -> 1)
 + (this/ValueSpecificationAction -> 1)
 + (this/TimeExpression -> 1)
 + (this/Duration -> 1)
 + (this/DurationInterval -> 1)
 + (this/TimeConstraint -> 1)
 + (this/TimeInterval -> 1)
 + (this/DurationConstraint -> 1)
 + (this/IntervalConstraint -> 1)
 + (this/Interval -> 1)
 + (this/Observation -> 1)
 + (this/TimeObservation -> 1)
 + (this/DurationObservation -> 1)
 + (this/InvocationAction -> 1)
 + (this/Trigger -> 1)
 + (this/StateMachine -> 1)
 + (this/Transition -> 2)
 + (this/Vertex -> 1)
 + (this/Pseudostate -> 1)
 + (this/FinalState -> 1)
 + (this/ConnectionPointReference -> 1)
 + (this/TimeEvent -> 1)
 + (this/Stereotype -> 1)
 + (this/Profile -> 1)
 + (this/Class -> 2)
 + (this/ProfileApplication -> 1)
 + (this/Extension -> 1)
 + (this/Image -> 1)
 + (this/Element -> 1)
 + (this/ExtensionEnd -> 1)
 + (this/VariableAction -> 1)
 + (this/ReadVariableAction -> 1)
 + (this/WriteVariableAction -> 1)
 + (this/ClearVariableAction -> 1)
 + (this/AddVariableValueAction -> 1)
 + (this/RemoveVariableValueAction -> 1)
 + (this/RaiseExceptionAction -> 1)
 + (this/ActionInputPin -> 1)
 + (this/GeneralizationSet -> 1)
 + (this/Generalization -> 1)
 + (this/InformationItem -> 1)
 + (this/InformationFlow -> 2)
 + (this/Model -> 1)
 + (this/ReadExtentAction -> 1)
 + (this/ReclassifyObjectAction -> 1)
 + (this/ReadIsClassifiedObjectAction -> 1)
 + (this/StartClassifierBehaviorAction -> 1)
 + (this/QualifierValue -> 1)
 + (this/LinkEndData -> 1)
 + (this/ReadLinkObjectEndAction -> 1)
 + (this/ReadLinkObjectEndQualifierAction -> 1)
 + (this/CreateLinkObjectAction -> 1)
 + (this/AcceptEventAction -> 1)
 + (this/AcceptCallAction -> 1)
 + (this/ReplyAction -> 1)
 + (this/UnmarshallAction -> 1)
 + (this/ReduceAction -> 1)
 + (this/JoinNode -> 1)
 + (this/DataStoreNode -> 1)
 + (this/ObjectFlow -> 1)
 + (this/ObjectNode -> 2)
 + (this/ParameterSet -> 1)
 + (this/Activity -> 1)
 + (this/Parameter -> 2)
 + (this/Action -> 1)
 + (this/InterruptibleActivityRegion -> 1)
 + (this/ActivityNode -> 1)
 + (this/BehavioralFeature -> 2)
 + (this/Behavior -> 1)
 + (this/Pin -> 2)
 + (this/ConditionalNode -> 1)
 + (this/StructuredActivityNode -> 3)
 + (this/LoopNode -> 1)
 + (this/Clause -> 1)
 + (this/ActivityEdge -> 1)
 + (this/ActivityGroup -> 1)
 + (this/ExpansionNode -> 1)
 + (this/ExpansionRegion -> 1)
 + (this/ExecutableNode -> 1)
 + (this/ExceptionHandler -> 1)
 + (this/Component -> 2)
 + (this/Deployment -> 1)
 + (this/DeploymentSpecification -> 1)
 + (this/ProtocolConformance -> 1)
 + (this/Interface -> 1)
 + (this/Port -> 1)
 + (this/ProtocolTransition -> 1)
 + (this/ProtocolStateMachine -> 1)
 + (this/State -> 3)
 + (this/Region -> 2)
 + (this/AssociationClass -> 2)
 + (this/TemplateSignature -> 1)
 + (this/NamedElement -> 1)
 + (this/TemplateParameter -> 1)
 + (this/StringExpression -> 2)
 + (this/TemplateBinding -> 1)
 + (this/TemplateParameterSubstitution -> 1)
 + (this/TemplateableElement -> 1)
 + (this/ParameterableElement -> 1)
 + (this/Property -> 4)
 + (this/ValueSpecification -> 2)
 + (this/Operation -> 3)
 + (this/OperationTemplateParameter -> 1)
 + (this/PackageableElement -> 2)
 + (this/Classifier -> 4)
 + (this/ClassifierTemplateParameter -> 1)
 + (this/RedefinableTemplateSignature -> 2)
 + (this/ConnectableElement -> 2)
 + (this/ConnectableElementTemplateParameter -> 1)
 + (this/Package -> 3)
}

