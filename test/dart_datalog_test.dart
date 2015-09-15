// Copyright (c) 2015, <your name>. All rights reserved. Use of this source code
// is governed by a BSD-style license that can be found in the LICENSE file.

library dart_datalog.test;

import 'package:dart_datalog/dart_datalog.dart';
import 'package:test/test.dart';


DLAtom gfather(x, y) => Fact("gfather", [x, y]);
DLAtom father(x, y) => Fact("father", [x, y]);
DLVariable X = V("X");
DLVariable Y = V("Y");
DLVariable Z = V("Z");
DLConst sam = C("sam");
DLConst old = C("old");
DLConst bob = C("bob");


void main() {
  group('Sample of formulas', () {

    setUp(() {

    });

    test('First', () {

      DL d = new DL();

      d.addRules([
      gfather(X, Y) <= father(X, Z) ^ father(Z, Y)
      ]);

      d.addFact(father(sam, bob));
      d.addFact(father(old, sam));

      expect(d.solveBU(gfather(V("A"), V("B"))), gfather(sam, bob));
      
    });
  });
}
