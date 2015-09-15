// Copyright (c) 2015, <your name>. All rights reserved. Use of this source code
// is governed by a BSD-style license that can be found in the LICENSE file.
library dart_datalog.base;

import 'package:vacuum_persistent/persistent.dart';
import 'package:quiver/core.dart' as quiver;

DLAtom Fact(String name, List<DLConstVar> args) => new DLAtom(name, (new LinkedListBuilder<DLConstVar>()..addAll(args)).build());
DLVariable V(String name) => new DLVariable(name);
DLConst C(dynamic item) => new DLConst(item);


class Substitution {
  PMap<DLVariable, DLConst> s;

  Substitution(this.s) {
    assert(this.s != null);
  }

  Substitution.empty() : this(new PMap());

  Substitution.single(DLVariable k, DLConst v) : this(new PMap().assoc(k, v));

  DLConst get(DLVariable k, [DLConst defaultV]) => s.get(k, defaultV);

  Substitution union(Substitution o) => o is Substitution ? new Substitution(s.union(o.s)) : o;

  String toString() => s.toString();

  operator ==(dynamic o) => o is Substitution && o.s == s;

  int get hashCode => s.hashCode;

}


abstract class DLTerm {

  DLTerm subst(Substitution subst);

  bool get isGround;
}

abstract class DLConstVar {

  Substitution unify(DLConstVar b);
}

class DLVariable extends DLConstVar {
  String name;
  DLVariable(String name) : this.name = name.toUpperCase();

  Substitution unify(DLConstVar b) => b is DLConst ? new Substitution.single(this, b) : new Substitution.empty();

  DLConstVar subst(Substitution s) {
    DLConst v = s.get(this);
    return v != null ? v : this;
  }

  String toString() => "${name}";

  operator ==(dynamic o) => o is DLVariable && o.name == name;

  int get hashCode => name.hashCode;
}

class DLAtom extends DLTerm {
  String fact;
  LinkedList<DLConstVar> args;

  DLAtom(this.fact, this.args);

  DLAtom subst(Substitution subst) => new DLAtom(fact, (new LinkedListBuilder()..addAll(args.map((x) => x.subst(subst)))).build());

  bool get isGround => args
      .where((x) => x is DLVariable)
      .isEmpty;

  operator <=(DLTerm right) => new DLRule(this, right);

  operator ^(DLAtom right) => new DLAnd(new PSet.from([this, right]));

  Substitution unify(DLTerm b) {
    if (!(b is DLAtom && fact == b.fact && args.length == b.args.length)) return new Substitution.empty();
    DLAtom atm = b as DLAtom;
    Substitution ret = new Substitution.empty();
    for (int i = 0; i < args.length; i++) {
      ret = ret.union(args.elementAt(i).unify(atm.args.elementAt(i)));
    }
    return ret;
  }

  operator ==(dynamic o) => o is DLAtom && o.fact == fact && o.args == args;

  int get hashCode => quiver.hash2(fact, args);

  String toString() => "$fact(${args.join(",")})";

}

class DLConst extends DLConstVar {
  dynamic item;

  DLConst(this.item);

  String toString() => "${this.item}";

  Substitution unify(DLConstVar b) => b is DLVariable ? new Substitution.single(b, this) : new Substitution.empty();

  DLConst subst(Substitution s) => this;

  operator ==(dynamic o) => o is DLConst && o.item == item;

  int get hashCode => item.hashCode;
}

class DLRule {
  DLAtom left;
  DLAnd right;

  DLRule(this.left, this.right);

  DLRule subst(Substitution subst) => new DLRule(left.subst(subst), right.subst(subst));

  operator ==(dynamic o) => o is DLRule && o.left == left && o.right == right;

  int get hashCode => quiver.hash2(left, right);

  String toString() => "$left := $right";
}

class DLAnd extends DLTerm {
  PSet<DLAtom> goals;

  DLAnd(this.goals);

  DLAnd.list(Iterable<DLAtom> l) : this(new PSet.from(l));

  DLAnd subst(Substitution subst) => new DLAnd(new PSet.from(goals.map((x) => x.subst(subst))));

  bool get isGround => goals.every((x) => x.isGround);

  operator ^(DLAtom right) => new DLAnd(goals.insert(right));

  operator ==(dynamic o) => o is DLAnd && goals == o.goals;

  int get hashCode => goals.hashCode;

  String toString() => "${goals.join(" & ")}";
}

class DL {

  TSet<DLRule> rules = new PSet().asTransient();
  TSet<DLAtom> kb = new PSet().asTransient();

  void addRule(DLRule rule) {
    rules.doInsert(rule);
  }

  void addRules(Iterable<DLRule> r) {
    for(DLRule rule in r) rules.doInsert(rule);
  }

  void addFact(DLAtom fact) {
    if(!fact.isGround) throw new Exception("Fact should be ground, no variables allowed");
    kb.doInsert(fact);
  }


  String toString() {
    StringBuffer sb = new StringBuffer();
    sb.write("Rules:\n");
    sb.write(rules.join("\n"));
    sb.write("\n\nFacts:\n");
    sb.write(kb.join("\n"));
    return sb.toString();
  }


  DLAtom solveBU(DLAtom query) {
    if(kb.isEmpty) return null;
    var matching = kb.firstWhere((fact) => unifiable(fact, query) != null, orElse:() => null);
    if (matching != null) {
      return unifiable(matching, query);
    }
    while (true) {
      TSet<DLAtom> newFacts = new PSet().asTransient();
      for(DLRule rule in rules) {
        LinkedList<PSet<Substitution>> subst = (new LinkedListBuilder()..addAll(
            rule.right.goals.map(
                (DLAtom goal) => new PSet.from(
                    kb.map(
                        (DLAtom fact) => fact.unify(goal)
                    )
                )
            )
        )).build();
        PSet<Substitution> candidate = flatten(subst);
        for(Substitution s in candidate) {
          if(rule.right.subst(s).isGround) {
            DLAtom newF = rule.left.subst(s);
            if(newF.isGround && !kb.contains(newF))
              newFacts.doInsert(newF);
          }
        }
      }
      if(newFacts.isEmpty) return null;
      var matching = newFacts.firstWhere((fact) => unifiable(fact, query) != null, orElse:() => null);
      if (matching != null) {
        return unifiable(matching, query);
      }

      for(DLAtom at in newFacts)
        kb.doInsert(at);
    }
  }

  PSet<Substitution> flatten(LinkedList<PSet<Substitution>> s) {
    if(s.isCons) {
      PSet<Substitution> tailflat = flatten(s.asCons.tail);
      TSet<Substitution> allSubst = new PSet().asTransient();
      for (Substitution scur in s.asCons.elem) {
        for (Substitution stail in tailflat) {
          allSubst.doInsert(scur.union(stail));
        }
      }
      return allSubst.asPersistent();
    }
    else return new PSet.from([new Substitution.empty()]);
  }

  DLTerm unifiable(DLAtom a, DLAtom b) {
    Substitution s = a.unify(b);
    DLTerm sa = a.subst(s);
    DLTerm sb = b.subst(s);
    if(sa == sb)
      return sa;
    else
      return null;
  }

}
