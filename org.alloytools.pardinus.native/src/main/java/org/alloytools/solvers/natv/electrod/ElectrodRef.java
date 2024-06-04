package org.alloytools.solvers.natv.electrod;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.AbortedException;
import kodkod.engine.InvalidSolverParamException;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.engine.TemporalSolver;
import kodkod.engine.UnboundedSolver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.Skolemizer;
import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.unbounded.InvalidUnboundedProblem;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.solvers.api.NativeCode;
import kodkod.solvers.api.TemporalSolverFactory;

import static kodkod.util.nodes.AnnotatedNode.annotateRoots;

abstract class ElectrodRef extends SATFactory implements TemporalSolverFactory {

    private static final long serialVersionUID = 1L;
    final File                electrod;
    final File                solver;
    final String              solverId;

    class ElectrodSolver implements UnboundedSolver<ExtendedOptions>, TemporalSolver<ExtendedOptions> {

        final ExtendedOptions options;

        ElectrodSolver(ExtendedOptions options) {
            if (options == null)
                throw new NullPointerException();
            this.options = options;
            if (!options.unbounded() && options.minTraceLength() != 1)
                throw new InvalidSolverParamException("Electrod bounded model checking must start at length 1.");
            if (options.noOverflow())
                throw new InvalidSolverParamException("Electrod model checking does not support preventing integer overflows.");

        }

        /**
         * {@inheritDoc}
         */
        public ExtendedOptions options() {
            return options;
        }

        /**
         * {@inheritDoc}
         */
        public Solution solve(Formula formula, PardinusBounds bounds) throws InvalidUnboundedProblem, InvalidUnboundedSolution {
            if (!options.decomposed() && bounds.amalgamated != null)
                bounds = bounds.amalgamated();

            options.reporter().solvingCNF(-1, -1, -1, -1);

            // retrieve the additional formula imposed by the symbolic
            // bounds, depending on execution stage
            Formula symbForm = Formula.TRUE;
            // if decomposed mode, the amalgamated bounds are always considered
            if (options.decomposed() && bounds.amalgamated() != null)
                symbForm = bounds.amalgamated().resolve(options.reporter());
                // otherwise use regular bounds
            else
                symbForm = bounds.resolve(options.reporter());
            // NOTE: this is already being performed inside the translator, but is not accessible
            formula = formula.and(symbForm);

            formula = Skolemizer.skolemize(annotateRoots(formula), bounds, options).node();
            Map<Relation, String> rel2name = new HashMap<>();
            String electrod = ElectrodPrinter.print(formula, bounds, rel2name, options);
            Solution solution;
            if (solverId == null) {
                try {
                    solution = Solution.unsatisfiable(null, null);
                    File f = Files.createTempFile(options.uniqueName(), ".elo").toFile();
                    write(f, electrod);
                    solution.setOutput(f);
                    return solution;
                } catch (Exception e) {
                    throw new RuntimeException(e);
                }
            } else {
                String xml = execute(this, electrod, bounds);
                ElectrodReader rd = new ElectrodReader(bounds,rel2name);
                TemporalInstance temporalInstance = rd.read(xml);
                Statistics stats = new Statistics(rd.nbvars, 0, 0, rd.ctime, rd.atime);
                solution = temporalInstance == null ? Solution.unsatisfiable(stats, null) : Solution.satisfiable(stats, temporalInstance);
            }
            return solution;
        }

    }

    ElectrodRef(String solver) {
        solverId = solver;
        this.electrod = NativeCode.platform.getExecutable("electrod").orElse(null);
        this.solver = solverId == null ? null : NativeCode.platform.getExecutable(solver).orElse(null);
    }

    @Override
    public boolean isPresent() {
        return electrod != null && solver != null;
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod", solverId
        };
    }


    @Override
    public boolean incremental() {
        return false;
    }

    @Override
    public boolean unbounded() {
        return true;
    }


    @Override
    public SATSolver instance() {
        return new ExternalSolver("electrod", null, true, "-t", solverId);
    }



    @Override
    public String type() {
        return "external";
    }


    @Override
    public TemporalSolver<ExtendedOptions> getTemporalSolver(ExtendedOptions options) {
        return new ElectrodSolver(options);
    }

    String execute(ElectrodSolver electrodSolver, String elo, PardinusBounds bounds) {
        Reporter reporter = electrodSolver.options.reporter();

        Process process = null;
        String output = null;
        Exception exception = null;
        int exitCode = Integer.MAX_VALUE;
        ProcessBuilder processBuilder = new ProcessBuilder();
        Map<String,String> environment = processBuilder.environment();
        environment.put("PATH", addSolverToPath(environment.get("PATH"), solver));
        List<String> args = processBuilder.command();
        args.add(electrod.getAbsolutePath());
        args.add("-t");
        args.add(solverId);
        if (ExtendedOptions.isDebug())
            args.add("-v");

        ExtendedOptions options = electrodSolver.options();
        if (!options.unbounded()) {
            args.add("--bmc");
            args.add(Integer.toString(options.maxTraceLength()));
        }

        try {
            File tempDir = Files.createTempDirectory(options.uniqueName()).toFile();
            File eloFile = new File(tempDir, "output.elo");
            write(eloFile, elo);
            File out = new File(tempDir, ".out");
            args.add(eloFile.getAbsolutePath());
            processBuilder.redirectError(out);
            processBuilder.redirectOutput(out);
            reporter.debug("starting electrod process with : " + args);

            process = processBuilder.start();
            exitCode = process.waitFor();
            output = read(out);

            if (exitCode == 0) {
                String xmlLink = String.format("%05d.xml", bounds.integration);
                File xmlFile = new File(tempDir, "output.xml");
                File link = new File(tempDir, xmlLink);
                Files.createLink(link.toPath(), xmlFile.toPath());
                return read(xmlFile);
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            exception = e;
        } catch (Exception e) {
            exception = e;
        } finally {
            if (process != null)
                process.destroy();
        }
        String report = "electrod exit code: " + exitCode + ":\n  args=" + args.stream().collect(Collectors.joining(" ")) + "\n  output=" + output;
        reporter.debug(report);
        throw new AbortedException(report);
    }

    private String addSolverToPath(String PATH, File solverPath) {
        String dir = solverPath.getParent();
        if (PATH == null) {
            return dir;
        } else
            return dir + File.pathSeparator + PATH;
    }

    private String read(File file) throws Exception {
        try {
            if (file != null && file.isFile()) {
                byte[] allBytes = Files.readAllBytes(file.toPath());
                return new String(allBytes, StandardCharsets.UTF_8);
            }
        } catch (Exception e) {
            return e.toString();
        }
        return "no file " + file;
    }

    private void write(File file, String contents) throws Exception {
        Files.write(file.toPath(), contents.getBytes(StandardCharsets.UTF_8));
    }

}
