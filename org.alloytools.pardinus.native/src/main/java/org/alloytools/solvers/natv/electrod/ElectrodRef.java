package org.alloytools.solvers.natv.electrod;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.List;
import java.util.stream.Collectors;

import kodkod.ast.Formula;
import kodkod.engine.AbortedException;
import kodkod.engine.InvalidSolverParamException;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.engine.TemporalSolver;
import kodkod.engine.UnboundedSolver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.unbounded.InvalidUnboundedProblem;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.solvers.api.NativeCode;
import kodkod.solvers.api.TemporalSolverFactory;

abstract class ElectrodRef extends SATFactory implements TemporalSolverFactory {

    private static final long serialVersionUID = 1L;
    final String              electrod;
    final String              solver;
    final String              solverId;

    class ElectrodSolver implements UnboundedSolver<ExtendedOptions>, TemporalSolver<ExtendedOptions> {

        final ExtendedOptions options;

        ElectrodSolver(ExtendedOptions options) {
            if (options == null)
                throw new NullPointerException();
            this.options = options;
            if (!options.unbounded()) {
                if (options.minTraceLength() != 1)
                    throw new InvalidSolverParamException("Electrod bounded model checking must start at length 1.");
            }
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
            Reporter rep = options.reporter();

            if (!options.decomposed() && bounds.amalgamated != null)
                bounds = bounds.amalgamated();

            options.reporter().solvingCNF(-1, -1, -1, -1);

            String electrod = ElectrodPrinter.print(formula, bounds, rep);
            String xml = execute(this, electrod, bounds);
            ElectrodReader rd = new ElectrodReader(bounds);
            TemporalInstance temporalInstance = rd.read(xml);
            Statistics stats = new Statistics(rd.nbvars, 0, 0, rd.ctime, rd.atime);
            return temporalInstance == null ? Solution.unsatisfiable(stats, null) : Solution.satisfiable(stats, temporalInstance);
        }

    }

    ElectrodRef(String solver) {
        solverId = solver;
        this.electrod = NativeCode.platform.getExecutable("electrod").map(File::getAbsolutePath).orElse(null);
        this.solver = NativeCode.platform.getExecutable(solver).map(File::getAbsolutePath).orElse(null);
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
        List<String> args = processBuilder.command();
        args.add(electrod);
        args.add("-t");
        args.add(solver);

        ExtendedOptions options = electrodSolver.options();
        if (!options.unbounded()) {
            args.add("--bmc");
            args.add(Integer.toString(options.maxTraceLength()));
        }

        try {
            File tempDir = Files.createTempDirectory(options.uniqueName()).toFile();
            File eloFile = new File(tempDir, "output.elo");
            File out = new File(tempDir, ".out");
            args.add(elo);
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

    private String read(File file) {
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


}
