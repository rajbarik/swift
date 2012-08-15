//===--- TypeCheckConstraints.cpp - Constraint-based Type Checking --------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2015 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// This file implements constraint-based type checking, including type
// inference.
//
//===----------------------------------------------------------------------===//
#include "TypeChecker.h"
#include "swift/AST/ASTVisitor.h"
#include "swift/AST/ASTWalker.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/raw_ostream.h"
#include <iterator>
#include <memory>
#include <utility>

using namespace swift;

namespace {
  class ConstraintSystem;
}

void *operator new(size_t bytes, ConstraintSystem& cs,
                   size_t alignment = 8);

inline void operator delete(void *, const ConstraintSystem &cs, size_t) {}

namespace {
  /// \brief The kind of literal that a type variable must be.
  enum class LiteralKind : char {
    None,
    Integer,
    Float,
    Character,
    String
  };

  class OverloadChoice;
}

//===--------------------------------------------------------------------===//
// Type variable implementation.
//===--------------------------------------------------------------------===//
#pragma mark Type variable implementation

/// \brief The implementation object for a type variable used within the
/// constraint-solving type checker.
///
/// The implementation object for a type variable contains information about
/// the type variable, where it was generated, what protocols it must conform
/// to, what specific types it might be and, eventually, the fixed type to
/// which it is assigned.
class TypeVariableType::Implementation {
  /// \brief The unique number assigned to this type variable.
  unsigned ID;

  /// \brief The expression that will be assigned this particular type, if
  /// any.
  Expr *TheExpr;

  /// \brief The archetype that this type variable describes.
  ArchetypeType *Archetype;

  /// \brief The fixed type of this type variable, once it has been assigned.
  Type Fixed;

  /// \brief If the type variable is known to have one of several given types,
  /// those types are listed here.
  ArrayRef<Type> Intersection;

  /// \brief The protocols to which this type variable must conform.
  ArrayRef<ProtocolDecl *> ConformsTo;

  /// \brief The kind of literal this must be, if any.
  /// FIXME: We'd rather replace this with a protocol conformance
  /// requirement.
  LiteralKind Literal;

public:
  explicit Implementation(unsigned ID, Expr *TheExpr)
    : ID(ID), TheExpr(TheExpr), Archetype(nullptr), Literal(LiteralKind::None)
  {
    if (TheExpr) {
      // If we have a literal expression, determine the literal kind.
      switch (TheExpr->getKind()) {
      case ExprKind::IntegerLiteral: Literal = LiteralKind::Integer; break;
      case ExprKind::FloatLiteral: Literal = LiteralKind::Float; break;
      case ExprKind::CharacterLiteral: Literal = LiteralKind::Character; break;
      case ExprKind::StringLiteral: Literal = LiteralKind::String; break;
      default: break;
      }
    }
  }

  explicit Implementation(unsigned ID, ArchetypeType *Archetype)
    : ID(ID), TheExpr(nullptr), Archetype(Archetype),
      Literal(LiteralKind::None) { }

  /// \brief Retrieve the unique ID corresponding to this type variable.
  unsigned getID() const { return ID; }
  
  /// \brief Retrieve the expression that will be assigned this particular
  /// type, if any.
  Expr *getExpr() const { return TheExpr; }

  /// \brief Retrieve the archetype that this type variable replaced.
  ArchetypeType *getArchetype() const { return Archetype; }

  /// \brief Retrieve the fixed type to which this type variable has been
  /// assigned, or a null type if this type variable has not yet been
  /// assigned.
  Type getFixedType() const { return Fixed; }

  /// \brief Assign a type to this particular type variable.
  void assignType(Type T) {
    assert(Fixed.isNull() && "Already assigned a type!");
    Fixed = T;
  }

  /// \brief For an intersection type, returns a non-empty array of
  /// types with which the current type intersections.
  ArrayRef<Type> getIntersection() const { return Intersection; }

  /// \brief Provide the set of intersection types for this type variable.
  void setIntersection(ArrayRef<Type> IS) { Intersection = IS; }

  /// \brief Retrieve the set of protocols to which this type variable
  /// must conform.
  ArrayRef<ProtocolDecl *> getConformsTo() const { return ConformsTo; }

  /// \brief Provide the set of protocols to which this type variable must
  /// conform.
  void setConformsTo(ArrayRef<ProtocolDecl *> ConformsTo) {
    this->ConformsTo = ConformsTo;
  }

  /// \brief Determine what kind of literal will be used to initialize
  /// this variable.
  LiteralKind getLiteralKind() const ;

  void print(llvm::raw_ostream &Out) {
    Out << "$T" << ID;
    if (!ConformsTo.empty()) {
      Out << " :";
      bool first = true;
      for (auto proto : ConformsTo) {
        if (first) {
          first = false;
        } else {
          Out << ", ";
        }

        Out << proto->getName().str();
      }
    }

    switch (Literal) {
    case LiteralKind::None: break;
    case LiteralKind::Integer: Out << " IntegerLiteral"; break;
    case LiteralKind::Float: Out << " FloatLiteral"; break;
    case LiteralKind::Character: Out << " CharacterLiteral"; break;
    case LiteralKind::String: Out << " StringLiteral"; break;
    }

    if (Fixed)
      Out << " as " << Fixed.getString();
  }
};

template<typename ...Args>
TypeVariableType *TypeVariableType::getNew(ASTContext &C, Args &&...args) {
  // FIXME: Use the constraint-system's local allocator!

  // Allocate memory
  void *mem = C.Allocate(sizeof(TypeVariableType) + sizeof(Implementation),
                         alignof(TypeVariableType));

  // Construct the type variable.
  auto *result = ::new (mem) TypeVariableType(C);

  // Construct the implementation object.
  new (result+1) TypeVariableType::Implementation(std::forward<Args>(args)...);
  
  return result;
}

void TypeVariableType::print(raw_ostream &OS) const {
  OS << "$T" << getImpl().getID();
}

//===--------------------------------------------------------------------===//
// Constraints
//===--------------------------------------------------------------------===//
#pragma mark Constraints

namespace {
  /// \brief Describes the kind of constraint placed on two type variables,
  /// arranged by decreasing strictness.
  enum class ConstraintKind : char {
    /// \brief The two types must be bound to the same type. This is the only
    /// symmetric constraint.
    Equal,
    /// \brief The first type is a "trivial" subtype of the second type,
    /// meaning that it is a subtype that is also guaranteed to have the same
    // in-memory representation.
    TrivialSubtype,
    /// \brief The first type is a subtype of the second type, i.e., a value
    /// of the type of the first type can be used wherever a value of the
    /// second type is expected.
    Subtype,
    /// \brief The first type is convertible to the second type.
    Conversion
  };

  /// \brief A constraint between two type variables.
  class Constraint {
    /// \brief The kind of constraint.
    ConstraintKind Kind;

    /// \brief The first type.
    Type First;

    /// \brief The second type.
    Type Second;

    /// \brief If non-null, the name of a member of the first type is that
    /// being related to the second type.
    Identifier Member;

    /// \brief Constraints are always allocated within a given constraint
    /// system.
    void *operator new(size_t) = delete;

  public:
    Constraint(ConstraintKind Kind, Type First, Type Second, Identifier Member)
      : Kind(Kind), First(First), Second(Second), Member(Member) { }

    // FIXME: Need some context information here.

    /// \brief Determine the kind of constraint.
    ConstraintKind getKind() const { return Kind; }

    /// \brief Retrieve the first type in the constraint.
    Type getFirstType() const { return First; }

    /// \brief Retrieve the second type in the constraint.
    Type getSecondType() const { return Second; }

    void print(llvm::raw_ostream &Out) {
      First->print(Out);
      switch (Kind) {
      case ConstraintKind::Equal: Out << " == "; break;
      case ConstraintKind::TrivialSubtype: Out << " <t "; break;
      case ConstraintKind::Subtype: Out << " < "; break;
      case ConstraintKind::Conversion: Out << " << "; break;
      }
      if (!Member.empty())
        Out << "'" << Member.str() << "' ";

      Second->print(Out);
    }

    void dump() { print(llvm::errs()); }

    void *operator new(size_t bytes, ConstraintSystem& cs,
                       size_t alignment = alignof(Constraint)) {
      return ::operator new (bytes, cs, alignment);
    }

    inline void operator delete(void *, const ConstraintSystem &cs, size_t) {}
  };

  /// \brief Describes a particular choice of a declaration from within a
  /// reference to an overloaded name.
  class OverloadChoice {
    /// \brief The overloaded expression from which we're making a selection.
    OverloadSetRefExpr *E;

    /// \brief The index into the list of candidates, which specifies which
    /// overload candidate this choice represents.
    unsigned Index;

    /// \brief The constraint system in which this overload choice was selected.
    ConstraintSystem *Constraints;

    /// \brief Overload choices are always allocated within a given constraint
    /// system.
    void *operator new(size_t) = delete;

  public:
    OverloadChoice(OverloadSetRefExpr *expr, unsigned index,
                   ConstraintSystem *constraints)
      : E(expr), Index(index), Constraints(constraints) { }

    /// \brief Retrieve the overloaded expression that this choice concerns.
    OverloadSetRefExpr *getExpr() const { return E; }

    /// \brief Retrieve the index into the overloaded expression that this
    /// choice represents.
    unsigned getIndex() const { return Index; }

    /// \brief Retrieve the declaraton that corresponds to this overload choice.
    ValueDecl *getDecl() const { return E->getDecls()[Index]; }

    /// \brief Retrieve the constraint system implied by this overload choice.
    ConstraintSystem *getConstraints() const { return Constraints; }

    void *operator new(size_t bytes, ConstraintSystem& cs,
                       size_t alignment = alignof(Constraint)) {
      return ::operator new (bytes, cs, alignment);
    }

    inline void operator delete(void *, const ConstraintSystem &cs, size_t) {}
  };

  /// \brief An overload set, which is a set of overloading choices from which
  /// only one can be selected.
  class OverloadSet {
    /// \brief The number of choices in the overload set.
    unsigned NumChoices;
    
    /// \brief Overload sets are always allocated within a given constraint
    /// system.
    void *operator new(size_t) = delete;

    OverloadSet(ArrayRef<OverloadChoice *> choices)
      : NumChoices(choices.size())
    {
      memmove(this+1, choices.data(), sizeof(OverloadChoice *)*choices.size());
    }

  public:
    /// \brief Retrieve the set of choices provided by this overload set.
    ArrayRef<OverloadChoice *> getChoices() const {
      return { reinterpret_cast<OverloadChoice * const *>(this + 1),
               NumChoices };
    }

    /// \brief Create a new overload set, using (and copying) the given choices.
    static OverloadSet *getNew(ConstraintSystem &CS,
                               ArrayRef<OverloadChoice *> choices);
  };

  //===--------------------------------------------------------------------===//
  // Constraint system
  //===--------------------------------------------------------------------===//
#pragma mark Constraint system

  /// \brief The kind of type matching to perform in matchTypes().
  enum class TypeMatchKind : char {
    /// \brief Require the types to match exactly.
    SameType,
    /// \brief Require the first type to be a "trivial" subtype of the second
    /// type or be an exact match.
    TrivialSubtype,
    /// \brief Require the first type to be a subtype of the second type
    /// (or be an exact match or trivial subtype).
    Subtype,
    /// \brief Requires the first type to be convertible to the second type,
    /// which includes exact matches and both forms of subtyping.
    Conversion
  };

  /// \brief Describes a system of constraints on type variables, the
  /// solution of which assigns concrete types to each of the type variables.
  /// Constraint systems are typically generated given an (untyped) expression.
  class ConstraintSystem {
    TypeChecker &TC;
    ConstraintSystem *Parent;
    llvm::BumpPtrAllocator Allocator;
    unsigned TypeCounter;
    SmallVector<TypeVariableType *, 16> TypeVariables;
    SmallVector<Constraint *, 16> Constraints;
    SmallVector<OverloadSet *, 4> UnresolvedOverloadSets;
    SmallVector<std::unique_ptr<ConstraintSystem>, 2> Children;

    unsigned assignTypeVariableID() {
      ConstraintSystem *topCS = this;
      while (topCS->Parent)
        topCS = topCS->Parent;
      return topCS->TypeCounter++;
    }

  public:
    ConstraintSystem(TypeChecker &TC, ConstraintSystem *Parent = nullptr)
      : TC(TC), Parent(Parent), TypeCounter(0) { }

    /// \brief Retrieve the type checker assciated 
    TypeChecker &getTypeChecker() const { return TC; }

    /// \brief Retrieve the AST context.
    ASTContext &getASTContext() const { return TC.Context; }

    /// \brief Create a new constraint system that is derived from this
    /// constraint system, referencing the rules of the parent system but
    /// also introducing its own (likely dependent) constraints.
    ConstraintSystem *createDerivedConstraintSystem() {
      auto result = new ConstraintSystem(TC, this);
      Children.push_back(std::unique_ptr<ConstraintSystem>(result));
      return result;
    }

    /// \brief Create a new type variable.
    template<typename ...Args>
    TypeVariableType *createTypeVariable(Args &&...args) {
      auto tv= TypeVariableType::getNew(TC.Context, assignTypeVariableID(),
                                        std::forward<Args>(args)...);
      TypeVariables.push_back(tv);
      return tv;
    }

    /// \brief Add a constraint to the constraint system.
    void addConstraint(ConstraintKind kind, Type first, Type second) {
      assert(first && "Missing first type");
      assert(second && "Missing first type");
      Constraints.push_back(new (*this) Constraint(kind, first, second,
                                                   Identifier()));
    }

    /// \brief Add a member constraint to the constraint system.
    /// FIXME: Document in a more sane manner.
    void addMemberConstraint(ConstraintKind kind, Type first,
                             Identifier member, Type second) {
      assert(first);
      assert(second);
      Constraints.push_back(new (*this) Constraint(kind, first, second,
                                                   member));
    }

    /// \brief "Open" the given type by replacing any occurrences of archetypes
    /// (including those implicit in unbound generic types) with fresh type
    /// variables.
    ///
    /// \param type The type to open.
    /// \returns The opened type, or \c type if there are no archetypes in it.
    Type openType(Type type);

    /// \brief Retrieve the type of a reference to the given value declaration.
    ///
    /// For references to polymorphic function types, this routine "opens up"
    /// the type by replacing each instance of an archetype with a fresh type
    /// variable.
    Type getTypeOfReference(ValueDecl *decl);

    /// \brief Retrieve the type of a reference to the given value declaration,
    /// as a member with a base of the given type.
    ///
    /// For references to polymorphic function types, this routine "opens up"
    /// the type by replacing each instance of an archetype with a fresh type
    /// variable.
    Type getTypeOfMemberReference(Type baseTy, ValueDecl *decl);

    /// \brief Add a new overload set to the list of unresolved overload
    /// sets.
    void addOverloadSet(OverloadSet *ovl) {
      UnresolvedOverloadSets.push_back(ovl);
    }

    /// \brief Retrieve the allocator used by this constraint system.
    llvm::BumpPtrAllocator &getAllocator() { return Allocator; }

    template <typename It>
    ArrayRef<typename std::iterator_traits<It>::value_type>
    allocateCopy(It start, It end) {
      typedef typename std::iterator_traits<It>::value_type T;
      T *result = (T*)Allocator.Allocate(sizeof(T)*(end-start), __alignof__(T));
      unsigned i;
      for (i = 0; start != end; ++start, ++i)
        new (result+i) T(*start);
      return ArrayRef<T>(result, i);
    }

    template<typename T>
    ArrayRef<T> allocateCopy(ArrayRef<T> array) {
      return allocateCopy(array.begin(), array.end());
    }

    /// \brief Generate constraints for the given (unchecked) expression.
    void generateConstraints(Expr *E);

    /// \brief The result of attempting to resolve a constraint or set of
    /// constraints.
    enum class SolutionKind : char {
      /// \brief The constraint has been solved completely, and provides no
      /// more information.
      Solved,
      /// \brief The constraint could not be solved at this point.
      Unsolved,
      /// \brief The constraint uncovers an inconsistency in the system.
      Error
    };

  private:
    /// \brief Flags that direct type matching.
    enum TypeMatchFlags {
      TMF_None = 0,

      /// \brief Indicates that we are in a context where we should be
      /// generating constraints for any unsolvable problems.
      ///
      /// This flag is automatically introduced when type matching destructures
      /// a type constructor (tuple, function type, etc.), solving that
      /// constraint while potentially generating others.
      TMF_GenerateConstraints = 0x01
    };

    /// \brief Subroutine of \c matchTypes(), which matches up two tuple types.
    SolutionKind matchTupleTypes(TupleType *tuple1, TupleType *tuple2,
                                 TypeMatchKind kind, unsigned flags,
                                 bool &trivial);

    /// \brief Subroutine of \c matchTypes(), which matches up two function
    /// types.
    SolutionKind matchFunctionTypes(FunctionType *func1, FunctionType *func2,
                                    TypeMatchKind kind, unsigned flags,
                                    bool &trivial);

    /// \brief Attempt to match up types \c type1 and \c type2, which in effect
    /// is solving the given type constraint between these two types.
    ///
    /// \param type1 The first type, which is on the left of the type relation.
    ///
    /// \param type2 The second type, which is on the right of the type relation.
    ///
    /// \param kind The kind of type match being performed, e.g., exact match,
    /// trivial subtyping, subtyping, or conversion.
    ///
    /// \param flags A set of flags composed from the TMF_* constants, which
    /// indicates how
    ///
    /// \param trivial Will be set false if any non-trivial subtyping or
    /// conversion is applied.
    ///
    /// \returns the result of attempting to solve this constraint.
    SolutionKind matchTypes(Type type1, Type type2, TypeMatchKind kind,
                            unsigned flags, bool &trivial);

    /// \brief Simplify the given constaint.
    SolutionKind simplifyConstraint(const Constraint &constraint);

  public:
    /// \brief Simplify the system of constraints, by breaking down complex
    /// constraints into simpler constraints.
    ///
    /// The result of simplification is a constraint system that consisting of
    /// only simple constraints relating type variables to each other or
    /// directly to fixed types. There are no constraints that involve
    /// type constructors on both sides. the simplified constraint system may,
    /// of course, include type variables for which we have constraints but
    /// no fixed type. Such type variables are left to the solver to bind.
    ///
    /// \returns true if an error occurred, false otherwise.
    bool simplify();

    void dump();
  };
}

void *operator new(size_t bytes, ConstraintSystem& cs,
                   size_t alignment) {
  return cs.getAllocator().Allocate(bytes, alignment);
}

OverloadSet *OverloadSet::getNew(ConstraintSystem &CS,
                                 ArrayRef<OverloadChoice *> choices) {
  unsigned size = sizeof(OverloadSet)
                + sizeof(OverloadChoice *) * choices.size();
  void *mem = CS.getAllocator().Allocate(size, alignof(OverloadSet));
  return ::new (mem) OverloadSet(choices);
}

Type ConstraintSystem::openType(Type startingType) {
  llvm::DenseMap<ArchetypeType *, TypeVariableType *> replacements;

  auto getTypeVariable = [&](ArchetypeType *archetype) -> TypeVariableType * {
    // Check whether we already have a replacement for this archetype.
    auto known = replacements.find(archetype);
    if (known != replacements.end())
      return known->second;

    // Create a new type variable to replace this archetype.
    auto tv = createTypeVariable(archetype);
    tv->getImpl().setConformsTo(archetype->getConformsTo());
    // FIXME: Associated types!
    replacements[archetype] = tv;
    return tv;
  };

  std::function<Type(Type)> replaceArchetypes;
  replaceArchetypes = [&](Type type) -> Type {
    // Replace archetypes with fresh type variables.
    if (auto archetype = dyn_cast<ArchetypeType>(type)) {
      return getTypeVariable(archetype);
    }

    // Create type variables for all of the archetypes in a polymorphic
    // function type.
    if (auto polyFn = dyn_cast<PolymorphicFunctionType>(type)) {
      for (auto archetype : polyFn->getGenericParams().getAllArchetypes())
        (void)getTypeVariable(archetype);

      // Transform the input and output types.
      Type inputTy = TC.transformType(polyFn->getInput(), replaceArchetypes);
      if (!inputTy)
        return Type();

      Type resultTy = TC.transformType(polyFn->getResult(), replaceArchetypes);
      if (!resultTy)
        return Type();

      // Build the resulting (non-polymorphic) function type.
      return FunctionType::get(inputTy, resultTy, TC.Context);
    }

    // FIXME: Unbound generic types.
    return type;
  };
  
  return TC.transformType(startingType, replaceArchetypes);
}

Type ConstraintSystem::getTypeOfReference(ValueDecl *value) {
  // Determine the type of the value, opening up that type if necessary.
  return openType(value->getTypeOfReference());
}

Type ConstraintSystem::getTypeOfMemberReference(Type baseTy, ValueDecl *value) {
  // Figure out the instance type used for the base.
  baseTy = baseTy->getRValueType();
  if (auto baseMeta = baseTy->getAs<MetaTypeType>())
    baseTy = baseMeta->getInstanceType();

  // Figure out the type of the owner.
  auto owner = value->getDeclContext();
  Type ownerTy;
  if (auto nominalOwner = dyn_cast<NominalTypeDecl>(owner)) {
    ownerTy = nominalOwner->getDeclaredTypeInContext();
  } else {
    auto extensionOwner = cast<ExtensionDecl>(owner);
    auto extendedTy = extensionOwner->getExtendedType();
    if (auto nominal = extendedTy->getAs<NominalType>())
      ownerTy = nominal->getDecl()->getDeclaredTypeInContext();
    else if (auto unbound = extendedTy->getAs<UnboundGenericType>())
      ownerTy = unbound->getDecl()->getDeclaredTypeInContext();
    else
      llvm_unreachable("unknown owner for type member");
  }

  if (ownerTy->isSpecialized()) {
    // If the owner is specialized, we need to open up the types in the owner.
    // FIXME: Implement this
    llvm_unreachable("opening of generic types unimplemented");
  }

  // The base type must be a subtype of the owner type.
  addConstraint(ConstraintKind::Subtype, baseTy, ownerTy);

  // Determine the type of the member.
  return openType(value->getTypeOfReference());
}

/// \brief Retrieve the name bound by the given (immediate) pattern.
static Identifier findPatternName(Pattern *pattern) {
  switch (pattern->getKind()) {
  case PatternKind::Paren:
  case PatternKind::Any:
  case PatternKind::Tuple:
    return Identifier();

  case PatternKind::Named:
    return cast<NamedPattern>(pattern)->getBoundName();

  case PatternKind::Typed:
    return findPatternName(cast<TypedPattern>(pattern)->getSubPattern());
  }

  llvm_unreachable("Unhandled pattern kind");  
}

//===--------------------------------------------------------------------===//
// Constraint generation
//===--------------------------------------------------------------------===//
#pragma mark Constraint generation

void ConstraintSystem::generateConstraints(Expr *expr) {
  class ConstraintGenerator : public ExprVisitor<ConstraintGenerator, Type> {
    ConstraintSystem &CS;

  public:
    ConstraintGenerator(ConstraintSystem &CS) : CS(CS) { }

    Type visitErrorExpr(ErrorExpr *E) {
      // FIXME: Can we do anything with error expressions at this point?
      return nullptr;
    }

    Type visitLiteralExpr(LiteralExpr *E) {
      // Literal expressions require that their type support the
      // (informal) protocol for the corresponding literal type.
      return CS.createTypeVariable(E);
    }

    Type visitDeclRefExpr(DeclRefExpr *E) {
      // FIXME: If the decl is in error, we get no information from this.
      // We may, alternatively, want to use a type variable in that case,
      // and possibly infer the type of the variable that way.
      return CS.getTypeOfReference(E->getDecl());
    }

    Type visitDotSyntaxBaseIgnoredExpr(DotSyntaxBaseIgnoredExpr *E) {
      llvm_unreachable("Already type-checked");
    }

    Type visitOverloadedDeclRefExpr(OverloadedDeclRefExpr *E) {
      // For a reference to an overloaded declaration, we create a type variable
      // that will be equal to different types in different child constraint
      // systems, one per overloaded declaration.
      auto tv = CS.createTypeVariable(E);
      ArrayRef<ValueDecl*> decls = E->getDecls();
      SmallVector<OverloadChoice *, 4> choices;
      for (unsigned i = 0, n = decls.size(); i != n; ++i) {
        // Create a new derived constraint system that captures the
        // additional requirements introduced by selecting this particular
        // overload.
        auto derivedCS = CS.createDerivedConstraintSystem();
        auto ovl = new (CS) OverloadChoice(E, i, derivedCS);
        choices.push_back(ovl);

        // Bind the type variable to the type of a reference to this declaration
        // within the derived constraint system.
        auto refTy = derivedCS->getTypeOfReference(decls[i]);
        derivedCS->addConstraint(ConstraintKind::Equal, refTy, tv);
      }

      // Record this overload set.
      CS.addOverloadSet(OverloadSet::getNew(CS, choices));
      return tv;
    }

    Type visitOverloadedMemberRefExpr(OverloadedMemberRefExpr *E) {
      // For a reference to an overloaded declaration, we create a type variable
      // that will be equal to different types in different child constraint
      // systems, one per overloaded declaration.
      // FIXME: Will this ever even happen? We'd need to resolve the 
      // base expression to a type before we ever get an overlaoded
      // member reference expression.
      auto tv = CS.createTypeVariable(E);
      ArrayRef<ValueDecl*> decls = E->getDecls();
      SmallVector<OverloadChoice *, 4> choices;
      auto baseTy = E->getBase()->getType();
      for (unsigned i = 0, n = decls.size(); i != n; ++i) {
        // Create a new derived constraint system that captures the
        // additional requirements introduced by selecting this particular
        // overload.
        auto derivedCS = CS.createDerivedConstraintSystem();
        auto ovl = new (CS) OverloadChoice(E, i, derivedCS);
        choices.push_back(ovl);

        auto decl = decls[i];

        // Bind the type variable to the type of a reference to this member
        // within the derived constraint system.
        auto refTy = derivedCS->getTypeOfMemberReference(baseTy, decl);
        derivedCS->addConstraint(ConstraintKind::Equal, refTy, tv);
      }
      
      // Record this overload set.
      CS.addOverloadSet(OverloadSet::getNew(CS, choices));
      return tv;
    }

    Type visitUnresolvedDeclRefExpr(UnresolvedDeclRefExpr *expr) {
      // This is an error case, where we're trying to use type inference
      // to help us determine which declaration the user meant to refer to.
      // FIXME: Do we need to note that we're doing some kind of recovery?
      return CS.createTypeVariable(expr);
    }

    Type visitMemberRefExpr(MemberRefExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitExistentialMemberRefExpr(ExistentialMemberRefExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitArchetypeMemberRefExpr(ArchetypeMemberRefExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitGenericMemberRefExpr(GenericMemberRefExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitUnresolvedMemberExpr(UnresolvedMemberExpr *expr) {
      auto tv = CS.createTypeVariable(expr);

      // The type must be a oneof type that has an element of the given name.
      // That named member has the type 'tv'.
      CS.addMemberConstraint(ConstraintKind::Equal, tv, expr->getName(),
                             tv);

      return tv;
    }

    Type visitUnresolvedDotExpr(UnresolvedDotExpr *expr) {
      // The base must have a member of the given name, such that accessing
      // that member through the base returns a value convertible to the type
      // of this expression.
      auto baseTy = expr->getBase()->getType();
      auto tv = CS.createTypeVariable(expr);
      CS.addMemberConstraint(ConstraintKind::Conversion, baseTy,
                             expr->getName(), tv);
      return tv;
    }

    Type visitSequenceExpr(SequenceExpr *expr) {
      llvm_unreachable("Didn't even parse?");
    }

    Type visitParenExpr(ParenExpr *expr) {
      return expr->getSubExpr()->getType();
    }

    Type visitTupleExpr(TupleExpr *expr) {
      // The type of a tuple expression is simply a tuple of the types of
      // its subexpressions.
      SmallVector<TupleTypeElt, 4> elements;
      elements.reserve(expr->getNumElements());
      for (unsigned i = 0, n = expr->getNumElements(); i != n; ++i) {
        elements.push_back(TupleTypeElt(expr->getElement(i)->getType(),
                                        expr->getElementName(i)));
      }

      return TupleType::get(elements, CS.getASTContext());
    }

    Type visitSubscriptExpr(SubscriptExpr *expr) {
      ASTContext &Context = CS.getASTContext();

      // The base type must have a subscript declaration with type 
      // I -> [byref] O, where I and O are fresh type variables. The index
      // expression must be convertible to I and the subscript expression
      // itself has type [byref] O.
      auto inputTv = CS.createTypeVariable(expr);
      auto outputTv = CS.createTypeVariable(expr);
      auto outputTy = LValueType::get(outputTv, 
                                      LValueType::Qual::DefaultForMemberAccess,
                                      Context);
      auto fnTy = FunctionType::get(inputTv, outputTy, Context);

      // Add the constraint for a subscript declaration.
      // FIXME: lame name!
      auto baseTy = expr->getBase()->getType();
      CS.addMemberConstraint(ConstraintKind::Equal, baseTy,
                             Context.getIdentifier("__subscript"), fnTy);
      
      // Add the constraint that the index expression's type be convertible
      // to the input type of the subscript operator.
      CS.addConstraint(ConstraintKind::Conversion,
                       expr->getIndex()->getType(),
                       inputTv);
      return outputTy;
    }

    Type visitOverloadedSubscriptExpr(OverloadedSubscriptExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitExistentialSubscriptExpr(ExistentialSubscriptExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitArchetypeSubscriptExpr(ArchetypeSubscriptExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitGenericSubscriptExpr(GenericSubscriptExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitTupleElementExpr(TupleElementExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    /// \brief Produces a type for the given pattern, filling in any missing
    /// type information with fresh type variables.
    ///
    /// \param pattern The pattern.
    /// \param expr The expression that 'anchors' the pattern, which is used
    /// to create fresh type variables.
    Type getTypeForPattern(Pattern *pattern, Expr *expr) {
      switch (pattern->getKind()) {
      case PatternKind::Paren:
        // Parentheses don't affect the type.
        return getTypeForPattern(cast<ParenPattern>(pattern)->getSubPattern(),
                                 expr);

      case PatternKind::Any:
      case PatternKind::Named:
        // For a pattern of unknown type, create a new type variable.
        return CS.createTypeVariable(expr);

      case PatternKind::Typed:
        // For a typed pattern, simply return the type of the pattern.
        // FIXME: Error recovery if the type is an error type?
        return cast<TypedPattern>(pattern)->getTypeLoc().getType();

      case PatternKind::Tuple: {
        auto tuplePat = cast<TuplePattern>(pattern);
        SmallVector<TupleTypeElt, 4> tupleTypeElts;
        tupleTypeElts.reserve(tuplePat->getNumFields());
        for (auto tupleElt : tuplePat->getFields()) {
          auto eltTy = getTypeForPattern(tupleElt.getPattern(), expr);
          auto name = findPatternName(tupleElt.getPattern());
          Type varArgBaseTy;
          if (tupleElt.isVararg()) {
            varArgBaseTy = eltTy;
            eltTy = CS.getTypeChecker().getArraySliceType(SourceLoc(), eltTy);
          }
          tupleTypeElts.push_back(TupleTypeElt(eltTy, name, tupleElt.getInit(),
                                               varArgBaseTy));
        }
        return TupleType::get(tupleTypeElts, CS.getASTContext());
      }
      }

      llvm_unreachable("Unhandled pattern kind");
    }

    Type visitFuncExpr(FuncExpr *expr) {
      // Func expressions always have function type. In cases where a parameter
      // or return type is omitted, a fresh type variable is used to stand in
      // for that parameter or return type, allowing it to be inferred from
      // context.
      auto funcTy = expr->getBodyResultTypeLoc().getType();
      if (!funcTy) {
        // If no return type was specified, create a fresh type
        // variable for it.
        funcTy = CS.createTypeVariable(expr);
      }

      // Walk through the patterns in the func expression, backwards,
      // computing the type of each pattern (which may involve fresh type
      // variables where parameter types where no provided) and building the
      // eventual function type.
      auto patterns = expr->getParamPatterns();
      for (unsigned i = 0, e = patterns.size(); i != e; ++i) {
        Type paramTy =  getTypeForPattern(patterns[e - i - 1], expr);
        funcTy = FunctionType::get(paramTy, funcTy, CS.getASTContext());
      }

      return funcTy;
    }

    Type visitExplicitClosureExpr(ExplicitClosureExpr *expr) {
      // Explicit closure expressions have function type (T1, T2, ..., TN) -> T0,
      // for fresh type variables Ti, 0 <= i <= N, where N is the number of
      // the largest closure argument (e.g., N=5 in an explicit closure { $5 }).
      unsigned n = expr->getParserVarDecls().size();
      SmallVector<TupleTypeElt, 4> tupleTypeElts;
      tupleTypeElts.reserve(n);
      for (unsigned i = 0; i != n; ++i) {
        tupleTypeElts.push_back(TupleTypeElt(CS.createTypeVariable(expr),
                                             Identifier()));
      }
      ASTContext &Context = CS.getASTContext();
      auto inputTy = TupleType::get(tupleTypeElts, Context);
      auto outputTy = CS.createTypeVariable(expr);
      return FunctionType::get(inputTy, outputTy, Context);
    }

    Type visitImplicitClosureExpr(ImplicitClosureExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitModuleExpr(ModuleExpr *expr) {
      // Module expressions always have a fixed type.
      return expr->getType();
    }

    Type visitAddressOfExpr(AddressOfExpr *expr) {
      return expr->getSubExpr()->getType();
    }

    Type visitNewArrayExpr(NewArrayExpr *expr) {
      // FIXME: Eventually, we'll want to support unbound generic types in
      // the type of the array-new expression, which requires opening up the
      // unbound generic type here.
      return expr->getType();
    }

    Type visitTypeOfExpr(TypeOfExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitOpaqueValueExpr(OpaqueValueExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitApplyExpr(ApplyExpr *expr) {
      ASTContext &Context = CS.getASTContext();
      
      // The function argument has some type (T1) -> T2 for fresh variables
      // T1 and T2.
      // FIXME: What if the function argument is a metatype?
      auto inputTy = CS.createTypeVariable(expr);
      auto outputTy = CS.createTypeVariable(expr);
      auto funcTy = FunctionType::get(ParenType::get(Context, inputTy),
                                      outputTy, Context);

      // FIXME: Allow conversions to function type? That seems completely
      // unnecessary... except perhaps for the metatype case mentioned above.
      CS.addConstraint(ConstraintKind::Equal, expr->getFn()->getType(), funcTy);

      // The argument type must be convertible to the input type.
      CS.addConstraint(ConstraintKind::Conversion, expr->getArg()->getType(),
                       inputTy);

      return outputTy;
    }

    Type visitImplicitConversionExpr(ImplicitConversionExpr *expr) {
      llvm_unreachable("Already type-checked");
    }

    Type visitCoerceExpr(CoerceExpr *expr) {
      llvm_unreachable("Already type-checked");
    }
  };

  class ConstraintWalker : public ASTWalker {
    ConstraintGenerator &CG;

  public:
    ConstraintWalker(ConstraintGenerator &CG) : CG(CG) { }

    virtual bool walkToExprPre(Expr *expr) {
      // Don't walk into the bodies of any function/closure expressions.
      if (isa<CapturingExpr>(expr)) {
        auto type = CG.visit(expr);
        expr->setType(type);
        return false;
      }
      
      return true;
    }

    /// \brief Once we've visited the children of the given expression,
    /// generate constraints from the expression.
    virtual Expr *walkToExprPost(Expr *expr) {
      auto type = CG.visit(expr);
      expr->setType(type);
      return expr;
    }

    /// \brief Ignore statements.
    virtual bool walkToStmtPre(Stmt *stmt) { return false; }

    /// \brief Ignore declarations.
    virtual bool walkToDeclPre(Decl *decl) { return false; }
  };

  // Walk the expression, generating constraints.
  ConstraintGenerator CG(*this);
  ConstraintWalker CW(CG);
  expr->walk(CW);
}

//===--------------------------------------------------------------------===//
// Constraint simplification
//===--------------------------------------------------------------------===//
#pragma mark Constraint simplification

ConstraintSystem::SolutionKind
ConstraintSystem::matchTupleTypes(TupleType *tuple1, TupleType *tuple2,
                                  TypeMatchKind kind, unsigned flags,
                                  bool &trivial) {
  // FIXME: When we're allowed to perform conversions, we can end up
  // shuffling here. Compute that shuffle.
  if (tuple1->getFields().size() != tuple2->getFields().size())
    return SolutionKind::Error;

  SolutionKind result = SolutionKind::Solved;
  unsigned subFlags = flags | TMF_GenerateConstraints;
  for (unsigned i = 0, n = tuple1->getFields().size(); i != n; ++i) {
    const auto &elt1 = tuple1->getFields()[i];
    const auto &elt2 = tuple2->getFields()[i];

    // FIXME: Any unlabeled cases we care about?
    if (elt1.getName() != elt2.getName())
      return SolutionKind::Error;

    if (elt1.isVararg() != elt2.isVararg())
      return SolutionKind::Error;

    switch (matchTypes(elt1.getType(), elt2.getType(), kind, subFlags,
                       trivial)) {
    case SolutionKind::Error:
      return SolutionKind::Error;

    case SolutionKind::Solved:
      break;

    case SolutionKind::Unsolved:
      result = SolutionKind::Unsolved;
      break;
    }
  }

  return result;
}

ConstraintSystem::SolutionKind
ConstraintSystem::matchFunctionTypes(FunctionType *func1, FunctionType *func2,
                                     TypeMatchKind kind, unsigned flags,
                                     bool &trivial) {
  // An [auto_closure] function type can be a subtype of a
  // non-[auto_closure] function type.
  if (func1->isAutoClosure() != func2->isAutoClosure()) {
    if (func2->isAutoClosure())
      return SolutionKind::Error;

    if (kind < TypeMatchKind::TrivialSubtype)
      return SolutionKind::Error;
  }

  // Determine how we match up the input/result types.
  TypeMatchKind subKind;
  switch (kind) {
  case TypeMatchKind::SameType:
  case TypeMatchKind::TrivialSubtype:
    subKind = kind;
    break;

  case TypeMatchKind::Subtype:
    subKind = TypeMatchKind::TrivialSubtype;
    break;

  case TypeMatchKind::Conversion:
    subKind = TypeMatchKind::Subtype;
    break;
  }

  unsigned subFlags = flags | TMF_GenerateConstraints;
  // Input types can be contravariant (or equal).
  SolutionKind result = matchTypes(func2->getInput(), func2->getInput(),
                                   subKind, subFlags, trivial);
  if (result == SolutionKind::Error)
    return SolutionKind::Error;

  // Result type can be covariant (or equal).
  switch (matchTypes(func1->getResult(), func2->getResult(), subKind,
                     subFlags, trivial)) {
  case SolutionKind::Error:
    return SolutionKind::Error;

  case SolutionKind::Solved:
    break;

  case SolutionKind::Unsolved:
    result = SolutionKind::Unsolved;
    break;
  }

  return result;
}

/// \brief Map a type-matching kind to a constraint kind.
static ConstraintKind getConstraintKind(TypeMatchKind kind) {
  switch (kind) {
  case TypeMatchKind::SameType:
    return ConstraintKind::Equal;

  case TypeMatchKind::TrivialSubtype:
    return ConstraintKind::TrivialSubtype;

  case TypeMatchKind::Subtype:
    return ConstraintKind::Subtype;

  case TypeMatchKind::Conversion:
    return ConstraintKind::Conversion;
  }

  llvm_unreachable("unhandled type matching kind");
}

ConstraintSystem::SolutionKind
ConstraintSystem::matchTypes(Type type1, Type type2, TypeMatchKind kind,
                             unsigned flags, bool &trivial) {
  // If we have type variables that have been bound to fixed types, look through
  // to the fixed type.
  auto typeVar1 = type1->getAs<TypeVariableType>();
  if (typeVar1 && typeVar1->getImpl().getFixedType()) {
    type1 = typeVar1->getImpl().getFixedType();
    typeVar1 = nullptr;
  }

  auto typeVar2 = type2->getAs<TypeVariableType>();
  if (typeVar2 && typeVar2->getImpl().getFixedType()) {
    type2 = typeVar2->getImpl().getFixedType();
    typeVar2 = nullptr;
  }

  // If the types are equivalent, we're done.
  if (type1->isEqual(type2))
    return SolutionKind::Solved;

  // If either (or both) types are type variables, unify the type variables.
  if (typeVar1 || typeVar2) {
    switch (kind) {
    case TypeMatchKind::SameType:
      if (typeVar1 && typeVar2) {
        // FIXME: Union-find magic to merge these type variables.
        return SolutionKind::Solved;
      }

      // Provide a fixed type for the type variable.
      if (typeVar1)
        typeVar1->getImpl().assignType(type2);
      else
        typeVar2->getImpl().assignType(type1);
      return SolutionKind::Solved;

    case TypeMatchKind::TrivialSubtype:
    case TypeMatchKind::Subtype:
    case TypeMatchKind::Conversion:
      if (flags & TMF_GenerateConstraints) {
        // Add a new constraint between these types. We consider the current
        // type-matching problem to the "solved" by this addition, because
        // this new constraint will be solved at a later point.
        // Obviously, this must not happen at the top level, or the algorithm
        // would not terminate.
        addConstraint(getConstraintKind(kind), type1, type2);
        return SolutionKind::Solved;
      }

      // We couldn't solve this constraint.
      return SolutionKind::Unsolved;
    }

    llvm_unreachable("Unhandled type-variable matching");
  }

  // Decompose parallel structure.
  auto canType1 = type1->getCanonicalType();
  auto canType2 = type2->getCanonicalType();
  unsigned subFlags = flags | TMF_GenerateConstraints;
  if (canType1->getKind() == canType2->getKind()) {
    switch (canType1->getKind()) {
#define SUGARED_TYPE(id, parent) case TypeKind::id:
#define TYPE(id, parent)
#include "swift/AST/TypeNodes.def"
      llvm_unreachable("Sugared type masquerading as canonical");

#define ALWAYS_CANONICAL_TYPE(id, parent) case TypeKind::id:
#define TYPE(id, parent)
#include "swift/AST/TypeNodes.def"
    case TypeKind::Error:
      return SolutionKind::Error;

    case TypeKind::UnstructuredUnresolved:
      llvm_unreachable("Unstructured unresolved type");

    case TypeKind::TypeVariable:
      llvm_unreachable("Type variables handled above");

    case TypeKind::Tuple: {
      auto tuple1 = cast<TupleType>(canType1);
      auto tuple2 = cast<TupleType>(canType2);
      return matchTupleTypes(tuple1, tuple2, kind, flags, trivial);
    }

    case TypeKind::OneOf:
    case TypeKind::Struct:
    case TypeKind::Class: {
      auto nominal1 = cast<NominalType>(canType1);
      auto nominal2 = cast<NominalType>(canType2);
      // FIXME: subtyping for classes!
      if (nominal1->getDecl() == nominal2->getDecl()) {
        return SolutionKind::Error;

        assert((bool)nominal1->getParent() == (bool)nominal2->getParent() &&
               "Mismatched parents of nominal types");

        if (!nominal1->getParent())
          return SolutionKind::Solved;

        // Match up the parents, exactly.
        return matchTypes(nominal1->getParent(), nominal2->getParent(),
                          TypeMatchKind::SameType, subFlags, trivial);
      }
      break;
    }

    case TypeKind::MetaType: {
      auto meta1 = cast<MetaTypeType>(canType1);
      auto meta2 = cast<MetaTypeType>(canType2);
      // FIXME: Subtyping among metatypes, for classes only?
      return matchTypes(meta1->getInstanceType(), meta2->getInstanceType(),
                        TypeMatchKind::SameType, subFlags, trivial);
    }

    case TypeKind::Function: {
      auto func1 = cast<FunctionType>(canType1);
      auto func2 = cast<FunctionType>(canType2);
      return matchFunctionTypes(func1, func2, kind, flags, trivial);
    }

    case TypeKind::PolymorphicFunction:
      llvm_unreachable("Polymorphic function type should have been opened");

    case TypeKind::Array: {
      auto array1 = cast<ArrayType>(canType1);
      auto array2 = cast<ArrayType>(canType2);
      return matchTypes(array1->getBaseType(), array2->getBaseType(),
                        TypeMatchKind::SameType, subFlags, trivial);
    }

    case TypeKind::ProtocolComposition:
      // Existential types handled below.
      break;

    case TypeKind::LValue: {
      auto lvalue1 = cast<LValueType>(canType1);
      auto lvalue2 = cast<LValueType>(canType2);
      if (lvalue1->getQualifiers() != lvalue2->getQualifiers() &&
          !(kind >= TypeMatchKind::TrivialSubtype &&
            lvalue1->getQualifiers() < lvalue2->getQualifiers()))
        return SolutionKind::Error;

      return matchTypes(lvalue1->getObjectType(), lvalue2->getObjectType(),
                        TypeMatchKind::SameType, subFlags, trivial);
    }

    case TypeKind::UnboundGeneric:
      llvm_unreachable("Unbound generic type should have been opened");

    case TypeKind::BoundGeneric: {
      auto bound1 = cast<BoundGenericType>(canType1);
      auto bound2 = cast<BoundGenericType>(canType2);
      
      // FIXME: subtyping for generic classes!
      if (bound1->getDecl() == bound2->getDecl()) {
        // Match up the parents, exactly, if there are parents.
        SolutionKind result = SolutionKind::Solved;
        assert((bool)bound1->getParent() == (bool)bound2->getParent() &&
               "Mismatched parents of bound generics");
        if (bound1->getParent()) {
          switch (matchTypes(bound1->getParent(), bound2->getParent(),
                             TypeMatchKind::SameType, subFlags, trivial)) {
          case SolutionKind::Error:
            return SolutionKind::Error;

          case SolutionKind::Solved:
            break;

          case SolutionKind::Unsolved:
            result = SolutionKind::Unsolved;
            break;
          }
        }

        // Match up the generic arguments, exactly.
        // FIXME: If this fails, do we have to look for a subtype?
        auto args1 = bound1->getGenericArgs();
        auto args2 = bound2->getGenericArgs();
        assert(args1.size() == args2.size() && "Mismatched generic args");
        for (unsigned i = 0, n = args1.size(); i != n; ++i) {
          switch (matchTypes(args1[i], args2[i], TypeMatchKind::SameType,
                             subFlags, trivial)) {
          case SolutionKind::Error:
            return SolutionKind::Error;

          case SolutionKind::Solved:
            break;

          case SolutionKind::Unsolved:
            result = SolutionKind::Unsolved;
            break;
          }
        }

        return result;
      }
      break;
    }
    }
  }

  // FIXME: Single type vs. tuple-of-one.
  // FIXME: Auto-closure.
  // FIXME: Materialization
  // FIXME: Loading values.

  if (kind >= TypeMatchKind::Conversion) {
    // An lvalue of type T2 can be converted to a value of type T1 so long as
    // T2 is convertible to T1 (by loading the value).
    if (auto lvalue2 = type2->getAs<LValueType>()) {
      return matchTypes(type1, lvalue2->getObjectType(), kind, subFlags,
                        trivial);
    }
  }

  // FIXME: Check existential types.
  // FIXME: Subtyping for class types.
  // FIXME: User-defined conversions.

  return SolutionKind::Error;
}

/// \brief Retrieve the type-matching kind corresponding to the given
/// constraint kind.
static TypeMatchKind getTypeMatchKind(ConstraintKind kind) {
  switch (kind) {
  case ConstraintKind::Equal: return TypeMatchKind::SameType;
  case ConstraintKind::TrivialSubtype: return TypeMatchKind::TrivialSubtype;
  case ConstraintKind::Subtype: return TypeMatchKind::Subtype;
  case ConstraintKind::Conversion: return TypeMatchKind::Conversion;
  }
}

ConstraintSystem::SolutionKind
ConstraintSystem::simplifyConstraint(const Constraint &constraint) {
  switch (constraint.getKind()) {
  case ConstraintKind::Equal:
  case ConstraintKind::TrivialSubtype:
  case ConstraintKind::Subtype:
  case ConstraintKind::Conversion: {
    // For relational constraints, match up the types.
    bool trivial = true;
    return matchTypes(constraint.getFirstType(), constraint.getSecondType(),
                      getTypeMatchKind(constraint.getKind()), TMF_None,
                      trivial);
  }
  }
}

bool ConstraintSystem::simplify() {
  bool solvedAny = false;
  do {
    // Loop through all of the thus-far-unsolved constraints, attempting to
    // simplify each one.
    SmallVector<Constraint *, 16> existingConstraints;
    existingConstraints.swap(Constraints);
    solvedAny = false;
    for (auto constraint : existingConstraints) {
      switch (simplifyConstraint(*constraint)) {
      case SolutionKind::Error:
        return true;

      case SolutionKind::Solved:
        // Implicitly drop this solved constraint.
        solvedAny = true;
        break;

      case SolutionKind::Unsolved:
        // Since this constraint was not solved, add it to the list of
        // remaining constraints.
        Constraints.push_back(constraint);
        break;
      }
    }
  } while (solvedAny);

  // We've solved all of the constraints we can.
  return false;
}

//===--------------------------------------------------------------------===//
// Debugging
//===--------------------------------------------------------------------===//
#pragma mark Debugging

void ConstraintSystem::dump() {
  llvm::raw_ostream &out = llvm::errs();

  out << "---Type Variables---\n";
  for (auto tv : TypeVariables) {
    out.indent(2);
    tv->getImpl().print(out);
    out << "\n";
  }

  out << "\n---Constraints---\n";
  for (auto constraint : Constraints) {
    out.indent(2);
    constraint->print(out);
    out << "\n";
  }
}

void TypeChecker::dumpConstraints(Expr *expr) {
  ConstraintSystem CS(*this);
  CS.generateConstraints(expr);
  llvm::errs() << "---Initial constraints for the given expression---\n";
  expr->dump();
  llvm::errs() << "\n";
  CS.dump();
  llvm::errs() << "---Simplified constraints---\n";
  bool error = CS.simplify();
  CS.dump();

  llvm::errs() << "\nConstraint system is "
               << (error? "ill-formed" : "still viable")
               << "\n";
}

