/**
 * Those classes are intended for users dealing with SAT solvers as black boxes.

<pre>
        ISolver solver = SolverFactory.defaultSolver();
        solver.setTimeout(3600); // 1 hour timeout
        Reader reader = new DimacsReader(solver);
        // CNF filename is given on the command line 
        try {
                IProblem problem = reader.parseInstance(args[0]);
                if (problem.isSatisfiable()) {
                        System.out.println("Satisfiable !");
                        System.out.println(reader.decode(problem.model()));
                } else {
                        System.out.println("Unsatisfiable !");
                }
        } catch (FileNotFoundException e) {
                // take action when the CNF file is not found
        } catch (ParseFormatException e) {
                // take action when the CNF file is not correctly formatted
        } catch (IOException e) {
                // take action if something really goes wrong
        } catch (ContradictionException e) {
                System.out.println("Unsatisfiable (trivial)!");
        } catch (TimeoutException e) {
                System.out.println("Timeout, sorry!");          
        }
        </pre>
 */

package org.sat4j.specs;

