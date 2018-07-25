/**
 *
 */
package examples.netconfig;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Pure Kodkod encoding of the new test case for ConfigAssure.
 *
 * @author Emina Torlak
 */
public final class ConfigAssure {

    /**
     * port is a unary relation that contains all the port atoms, represented by
     * concatenating the device name and the interface of each port.
     **/
    private final Relation    port;

    /**
     * unknown contains ports whose components aren't fully specified.
     */
    private final Relation    unknown;

    /**
     * The addr relation maps port atoms to all the power-of-2 atoms (1, 2, 4, ...,
     * 2^31).
     */
    private final Relation    addr;

    /**
     * The subnet relation maps one representative port atom in each subnet to all
     * the other port atoms in the same subnet. For example, the Prolog predicate
     * subnet(['IOS_00037'-'Vlan790', 'IOS_00038'-'Vlan790']) is represented by the
     * tuples <'IOS_00037'-'Vlan790', 'IOS_00037'-'Vlan790'> and
     * <'IOS_00037'-'Vlan790', 'IOS_00038'-'Vlan790'> in the subnet relation. We
     * choose the first port in each Prolog predicate that has a constant address
     * and mask to be the representative of that subnet, if such a port exists.
     * Otherwise, we choose the first Prolog predicate encountered during parsing to
     * be the representative of a given subnet. This encoding assumes that each port
     * can participate in at most one subnet.
     */
    private final Relation    subnet;

    /**
     * The group relation maps all atoms in each subnet that have the same interface
     * to one representative port atom. For example, the Prolog predicate
     * subnet(['IOS_00091'-'Vlan820', 'IOS_00092'-'Vlan820',
     * 'IOS_00096'-'FastEthernet0/0']) is represented by the tuples
     * <'IOS_00091'-'Vlan820', 'IOS_00091'-'Vlan820'>, <'IOS_00092'-'Vlan820',
     * 'IOS_00091'-'Vlan820>, and
     * <'IOS_00096'-'FastEthernet0/0','IOS_00096'-'FastEthernet0/0'> in the group
     * relation. Ports that are not part of any subnet form their own group (of
     * which they are a representative).
     */
    private final Relation    group;

    /**
     * The groupMask relation maps port atoms that are group representatives to the
     * integer atoms 1, 2, 4, 8 and 16, implicitly representing each group's mask by
     * the number of zeros it contains [0..31].
     **/
    private final Relation    groupMask;

    /**
     * Join of the group relation with the groupMask relation: provides an implicit
     * mask for each port.
     */
    private final Expression  mask;

    private final IntConstant ones    = IntConstant.constant(-1);
    private final static int  minAddr = (121 << 24) | (96 << 16);
    private final static int  maxAddr = minAddr | (255 << 8) | 255;

    /**
     * Constructs a new instance of ConfigAssure.
     */
    public ConfigAssure() {
        this.port = Relation.unary("port");
        this.unknown = Relation.unary("unknown");
        this.addr = Relation.binary("addr");
        this.groupMask = Relation.binary("groupMask");
        this.subnet = Relation.binary("subnet");
        this.group = Relation.binary("group");
        this.mask = group.join(groupMask);
    }

    /**
     * Returns the netID of the given port.
     *
     * @return netID of the given port
     */
    IntExpression netid(Expression p) {
        return addr(p).and(explicitMask(p));
    }

    /**
     * Returns the ip address of the given port.
     *
     * @return ip address of the given port
     */
    IntExpression addr(Expression p) {
        return p.join(addr).sum();
    }

    /**
     * Returns the number of zeros in the mask of the given port.
     *
     * @return the number of zeros in the mask of the given port
     */
    IntExpression implicitMask(Expression p) {
        return p.join(mask).sum();
    }

    /**
     * Returns the explicit mask of the given port.
     *
     * @return explicit mask of the given port
     */
    IntExpression explicitMask(Expression p) {
        return ones.shl(implicitMask(p));
    }

    /**
     * Returns the subnet of the given port.
     *
     * @return subnet of the given port
     */
    Expression subnet(Expression p) {
        return p.join(subnet);
    }

    /**
     * Returns a Formula that evaluates to true if the netid represented of the port
     * p0 contains the netid of the port p1.
     *
     * @return zeros(p0) >= zeros(p1) and (addr(p0) & mask(p0)) = (addr(p1) &
     *         mask(p0))
     */
    Formula contains(Expression p0, Expression p1) {
        final Formula f0 = implicitMask(p0).gte(implicitMask(p1));
        final Formula f1 = addr(p0).and(explicitMask(p0)).eq(addr(p1).and(explicitMask(p0)));
        return f0.and(f1);
    }

    /**
     * Returns the requirements.
     *
     * @return requirements
     */
    public Formula requirements() {

        final List<Formula> reqs = new ArrayList<Formula>();

        final Variable p0 = Variable.unary("p0"), p1 = Variable.unary("p1"), p2 = Variable.unary("p2");

        // contains the representatives of all subnets
        final Expression subreps = subnet.join(port);
        // contains the representatives of subnets with some unknown members
        final Expression unknownSubs = subnet.join(unknown);

        // the ports with known components are guaranteed to obey the following
        // constraints (ensured by the preprocessing steps).

        // no two ports on the same subnet (with some unknown ports) have the
        // same address:
        // all p0: unknownSubs, p1: unknown & p0.subnet, p2: p0.subnet - p1 |
        // addr(p1) != addr(p2)
        final Expression submembers = p0.join(subnet);
        reqs.add(addr(p1).eq(addr(p2)).not().forAll(p0.oneOf(unknownSubs).and(p1.oneOf(submembers.intersection(unknown))).and(p2.oneOf(submembers.difference(p1)))));

        // all ports on the same subnet (with some unknown ports) have the same
        // netid:
        // all p0: unknownSubs, p1: p0.subnet | netid(p0) = netid(p1)
        reqs.add(netid(p0).eq(netid(p1)).forAll(p0.oneOf(unknownSubs).and(p1.oneOf(submembers))));

        // netids of subnets with unknown representatives don't overlap with
        // netids of any other subnet:
        // all p0: subreps & unknown, p1: subreps- p0 | not contains(p0, p1) and
        // not contains(p1, p0)
        reqs.add(contains(p0, p1).not().and(contains(p1, p0).not()).forAll(p0.oneOf(subreps.intersection(unknown)).and(p1.oneOf(subreps.difference(p0)))));

        return Formula.and(reqs);
    }

    /**
     * Returns a new universe that contains the given ports atoms, followed by
     * Integer objects containing powers of 2 (1, 2, 4, ..., 2^31).
     */
    private final Universe universe(Set<String> ports) {
        final List<Object> atoms = new ArrayList<Object>(ports.size() + 32);
        atoms.addAll(ports);
        for (int i = 0; i < 32; i++) {
            atoms.add(Integer.valueOf(1 << i));
        }
        return new Universe(atoms);
    }

    /**
     * Returns a tupleset that maps the given port atom to each non-zero bit in the
     * given bit string.
     *
     * @return a tupleset that maps the given port atom to each non-zero bit in the
     *         given bit string.
     */
    private final TupleSet portToBits(TupleFactory factory, String port, int bits) {
        final TupleSet s = factory.noneOf(2);
        for (int i = 0, max = 32 - Integer.numberOfLeadingZeros(bits); i < max; i++) {
            if ((bits & (1 << i)) != 0)
                s.add(factory.tuple(port, Integer.valueOf(1 << i)));
        }
        return s;
    }

    /**
     * Returns the bounds corresponding to the given ip address and subnet files.
     *
     * @return bounds corresponding to the given ip address and subnet files.
     * @throws IOException if either of the files cannot be found or accessed
     * @throws IllegalArgumentException if either of the files cannot be parsed
     */
    public Bounds bounds(String ipAddrsFile, String subnetsFile) throws IOException {
        final Map<String,NetNode> nodes = parseAddresses(ipAddrsFile);
        final Map<NetNode,Subnet> subnets = parseSubnets(subnetsFile, nodes);

        final Universe universe = universe(nodes.keySet());
        final Bounds bounds = new Bounds(universe);
        final TupleFactory factory = universe.factory();

        // bind the integers
        for (int i = 0; i < 32; i++) {
            bounds.boundExactly(1 << i, factory.setOf(Integer.valueOf(1 << i)));
        }

        // bind the port relation exactly to the port names
        bounds.boundExactly(port, factory.range(factory.tuple(universe.atom(0)), factory.tuple(universe.atom(nodes.keySet().size() - 1))));

        // bind the unknown relation exactly to the port names of ports with
        // unknown addresses or masks
        final TupleSet unknownBound = factory.noneOf(1);
        for (NetNode n : nodes.values()) {
            if (!n.known()) {
                unknownBound.add(factory.tuple(n.port));
            }
        }
        bounds.boundExactly(unknown, unknownBound);

        // bind the subnet relation exactly, choosing the first element of each
        // subnet as the representative
        final TupleSet subnetBound = factory.noneOf(2);
        for (Map.Entry<NetNode,Subnet> entry : subnets.entrySet()) {
            final NetNode rep = entry.getKey();
            for (NetNode member : entry.getValue().members) {
                subnetBound.add(factory.tuple(rep.port, member.port));
            }
        }
        bounds.boundExactly(subnet, subnetBound);

        // bind the addr relation so that each address is guaranteed to be
        // between minAddr (121.96.0.0) and maxAddr (121.96.255.255), inclusive
        final TupleSet lAddr = factory.noneOf(2), uAddr = factory.noneOf(2);
        for (NetNode node : nodes.values()) {
            if (node.varAddress) { // unknown address
                lAddr.addAll(portToBits(factory, node.port, minAddr));
                uAddr.addAll(portToBits(factory, node.port, maxAddr));
            } else { // known address
                final TupleSet portToAddrBits = portToBits(factory, node.port, node.address);
                lAddr.addAll(portToAddrBits);
                uAddr.addAll(portToAddrBits);
            }
        }
        bounds.bound(addr, lAddr, uAddr);

        // bind the group and groupMask relations so that all ports with the
        // same interface on the same subnet are guaranteed to have the same
        // mask
        final TupleSet lMask = factory.noneOf(2), uMask = factory.noneOf(2), groupBound = factory.noneOf(2);
        for (Subnet sub : subnets.values()) {
            for (Map.Entry<NetNode,Set<NetNode>> entry : sub.groups.entrySet()) {
                final NetNode rep = entry.getKey();
                for (NetNode member : entry.getValue()) {
                    groupBound.add(factory.tuple(member.port, rep.port));
                    nodes.remove(member.port); // remove a grouped member out of
                                              // the addresses set
                }
                if (rep.varMask) { // unknown mask for the representative
                    uMask.addAll(portToBits(factory, rep.port, 31));
                } else { // known mask for the representative
                    final TupleSet portToMaskBits = portToBits(factory, rep.port, rep.mask);
                    lMask.addAll(portToMaskBits);
                    uMask.addAll(portToMaskBits);
                }
            }
        }

        // bind the group and groupMask relations for ports that are not a part
        // of any subnet
        for (NetNode ungrouped : nodes.values()) {
            groupBound.add(factory.tuple(ungrouped.port, ungrouped.port));
            if (ungrouped.varMask) { // unknown mask for the representative
                uMask.addAll(portToBits(factory, ungrouped.port, 31));
            } else { // known mask for the representative
                final TupleSet portToMaskBits = portToBits(factory, ungrouped.port, ungrouped.mask);
                lMask.addAll(portToMaskBits);
                uMask.addAll(portToMaskBits);
            }
        }

        bounds.bound(groupMask, lMask, uMask);
        bounds.boundExactly(group, groupBound);

        // System.out.println("groupMask.size: " + uMask.size() + ", group.size:
        // " + groupBound.size());
        // System.out.println("ports.size: " + bounds.upperBound(port).size() +
        // ", unknown.size: " + unknownBound.size());
        return bounds;

    }

    /**
     * Returns a string representation of the given bit string in the quad notation.
     *
     * @return a string representation of the given bit string in the quad notation.
     */
    private static final String toQuad(int bits) {
        return (bits >>> 24) + "." + ((bits >>> 16) & 255) + "." + ((bits >>> 8) & 255) + "." + (bits & 255) + ".";
    }

    /**
     * Displays an instance obtained with the given options.
     *
     * @requires inst != null and opt != null
     */
    private final void display(Instance inst, Options opt) {
        final Universe univ = inst.universe();
        final Evaluator eval = new Evaluator(inst, opt);
        final TupleFactory factory = univ.factory();
        final List<TupleSet> subnets = new ArrayList<TupleSet>();

        System.out.println("address\t\tnetwork id\tmask\tdevice-interface");
        for (int i = 0, ports = univ.size() - 32; i < ports; i++) {
            final Object atom = univ.atom(i);
            final Relation p = Relation.unary(atom.toString());
            inst.add(p, factory.setOf(atom));

            System.out.print(toQuad(eval.evaluate(addr(p))) + "\t");
            System.out.print(toQuad(eval.evaluate(netid(p))) + "\t");
            System.out.print(eval.evaluate(implicitMask(p)) + "\t");
            System.out.println(p);

            final TupleSet members = eval.evaluate(subnet(p));
            if (!members.isEmpty())
                subnets.add(members);
        }

        System.out.println("\nsubnets:");
        for (TupleSet sub : subnets) {
            System.out.println(sub);
        }

    }

    private static void usage() {
        System.out.println("java examples.ConfigAssure <ipAddresses file> <subnets file>");
        System.exit(1);
    }

    /**
     * Usage: java examples.ConfigAssure <ipAddresses file> <subnets file>
     */
    public static void main(String[] args) {
        if (args.length < 2)
            usage();
        try {
            final ConfigAssure ca = new ConfigAssure();
            final Solver solver = new Solver();
            solver.options().setBitwidth(32);
            solver.options().setSolver(SATFactory.MiniSat);

            final Formula formula = ca.requirements();
            final Bounds bounds = ca.bounds(args[0], args[1]);

            System.out.println("---explicit requirements (others are implicit in the bounds)---");
            System.out.println(PrettyPrinter.print(formula, 2));

            System.out.println("\n---solving with config files " + args[0] + " and " + args[1] + "---");

            final Solution sol = solver.solve(formula, bounds);

            System.out.println("\n---OUTCOME---");
            System.out.println(sol.outcome());

            System.out.println("\n---STATS---");
            System.out.println(sol.stats());

            if (sol.instance() != null) {
                System.out.println("\n---INSTANCE--");
                ca.display(sol.instance(), solver.options());
            }
        } catch (IOException ioe) {
            ioe.printStackTrace();
            usage();
        }
    }

    /**
     * Parses the given ipAddresses file and returns a map that binds each port name
     * in the file to its corresponding IPAddress record.
     *
     * @return a map that binds each port name in the given file to its
     *         corresponding IPAddress record.
     * @throws IOException
     */
    private static Map<String,NetNode> parseAddresses(String ipAddrsFile) throws IOException {
        final Map<String,NetNode> nodes = new LinkedHashMap<String,NetNode>();
        final BufferedReader reader = new BufferedReader(new FileReader(new File(ipAddrsFile)));
        for (String line = reader.readLine(); line != null; line = reader.readLine()) {
            final NetNode node = new NetNode(line);
            if (nodes.put(node.port, node) != null)
                throw new IllegalArgumentException("Duplicate ip address specification: " + line);
        }
        return nodes;
    }

    /**
     * Returns a map of each representative IPAddress to its subnet, as specified by
     * the given file and addresses.
     *
     * @return a map of each representative IPAddress to its subnet, as specified by
     *         the given file and addresses.
     * @throws IOException
     */
    private static Map<NetNode,Subnet> parseSubnets(String subnetsFile, Map<String,NetNode> addresses) throws IOException {
        final Map<NetNode,Subnet> subnets = new LinkedHashMap<NetNode,Subnet>();
        final BufferedReader reader = new BufferedReader(new FileReader(new File(subnetsFile)));
        for (String line = reader.readLine(); line != null; line = reader.readLine()) {
            final Subnet sub = new Subnet(line, addresses);
            subnets.put(sub.representative(), sub);
        }
        // check that all known representatives have disjoint netids
        for (NetNode n1 : subnets.keySet()) {
            for (NetNode n2 : subnets.keySet()) {
                if (n1 != n2) {
                    if (n1.known() && n2.known() && (n1.contains(n2) || n2.contains(n1))) {
                        throw new IllegalArgumentException("Netids of members of different subnets cannot overlap: " + n1 + ".netid = " + n2 + ".netid");
                    }
                }
            }
        }
        return subnets;
    }

    /**
     * A record containing the information parsed out of a Prolog ipAddress
     * predicate, e.g. ipAddress('IOS_00008', 'Vlan608', int(0), mask(1)).
     *
     * @specfield device, interfaceName, port: String
     * @specfield varAddress, varMask: boolean // true if the address (resp. mask)
     *            are variables
     * @specfield address, mask: int // variable or constant identifier of the
     *            address or mask
     * @invariant port = device + "-" + port
     * @invariant !varAddress => (minAddr <= address <= maxAddr)
     * @invariant !varMask => (0 <= mask <= 31)
     * @author Emina Torlak
     */
    private static class NetNode {

        final String                 device, interfaceName, port;
        final boolean                varAddress, varMask;
        final int                    address, mask;

        private static final Pattern pAddress = Pattern.compile("ipAddress\\((.+), (.+), (\\S+), (\\S+)\\)\\.");
        private static final Pattern pAddrVar = Pattern.compile("int\\((\\d+)\\)");
        private static final Pattern pMaskVar = Pattern.compile("mask\\((\\d+)\\)");

        private static final Matcher mAddress = pAddress.matcher("");
        private static final Matcher mAddrVar = pAddrVar.matcher(""), mMaskVar = pMaskVar.matcher("");

        /**
         * Constructs an IP address object using the provided ipAddress string.
         */
        NetNode(String addrString) {
            if (mAddress.reset(addrString).matches()) {
                this.device = mAddress.group(1);
                this.interfaceName = mAddress.group(2);
                this.port = device + "-" + interfaceName;
                if (mAddrVar.reset(mAddress.group(3)).matches()) {
                    this.varAddress = true;
                    this.address = Integer.parseInt(mAddrVar.group(1));
                } else {
                    this.varAddress = false;
                    this.address = parseConstant(mAddress.group(3), minAddr, maxAddr, "Expected the address to be a variable spec, int(<number>), or a number between " + minAddr + " and " + maxAddr + ", inclusive: " + addrString);
                }
                if (mMaskVar.reset(mAddress.group(4)).matches()) {
                    this.varMask = true;
                    this.mask = Integer.parseInt(mMaskVar.group(1));
                } else {
                    this.varMask = false;
                    this.mask = parseConstant(mAddress.group(4), 0, 31, "Expected the mask to be a variable spec, mask(<number>), or a number between 0 and 31, inclusive: " + addrString);
                }
            } else {
                throw new IllegalArgumentException("Unrecognized IP Address format: " + addrString);
            }
        }

        /**
         * Returns the netid of this port.
         *
         * @requires this.known
         * @return this.address & (-1<<this.mask)
         */
        int netid() {
            return address & (-1 << mask);
        }

        /**
         * Returns true if this net node is fully specified.
         *
         * @return !varAddress && !varMask
         */
        boolean known() {
            return !varAddress && !varMask;
        }

        /**
         * Returns true if this address and mask contains the other.
         *
         * @requires this.known && other.known
         * @return this.mask >= other.mask and (this.address & (-1<<this.mask)) =
         *         (other.address & (-1<<this.mask))
         */
        boolean contains(NetNode other) {
            return mask >= other.mask && (this.address & (-1 << mask)) == (other.address & (-1 << mask));
        }

        /**
         * Returns the integer value embedded in the given string iff it is between min
         * and max, inclusive. Otherwise throws an illegal argument exception with the
         * given message.
         */
        private static int parseConstant(String value, int min, int max, String msg) {
            try {
                final int val = Integer.parseInt(value);
                if (min <= val && val <= max) {
                    return val;
                }
            } catch (NumberFormatException nfe) {}
            throw new IllegalArgumentException(msg);
        }
    }

    /**
     * A record containing the information parsed out of a Prolog subnet predicate,
     * e.g. subnet(['IOS_00091'-'Vlan820', 'IOS_00092'-'Vlan820',
     * 'IOS_00096'-'FastEthernet0/0']).
     *
     * @specfield member: some IPAddress // members of this subnet
     * @specfield groups: member one-> member
     * @specfield representative: member
     * @invariant all rep: groups.member, m: groups[rep] | rep.interfaceName =
     *            m.interfaceName and (!rep.varMask => !m.varMask else (m.varMask =>
     *            m.mask = rep.mask))
     * @invariant all disj m1, m2: member | (!m1.varAddress and !m2.varAddress) =>
     *            m1.address != m2.address
     * @invariant all disj m1, m2: member | (!m1.varAddress and !m2.varAddress and
     *            !m1.varMask and !m2.varMask) => m1.netid() = m2.netid()
     * @invariant (representative.varAddress && representative.varMask) => (all m:
     *            member | m.varAddress && m.varMask)
     * @author Emina Torlak
     */
    private static class Subnet {

        final Set<NetNode>              members;
        final Map<NetNode,Set<NetNode>> groups;

        private static final Pattern    pSubnet    = Pattern.compile("subnet\\(\\[(.+)\\]\\)\\.");
        private static final Pattern    pSubMember = Pattern.compile(",*\\s*([^,]+)");
        private static final Matcher    mSubnet    = pSubnet.matcher(""), mSubMember = pSubMember.matcher("");

        /**
         * Constructs a subnet object out of the given subnet string and addresses.
         */
        Subnet(String subnetString, Map<String,NetNode> addresses) {
            this.members = members(subnetString, addresses);
            this.groups = groups(subnetString, members);
        }

        /**
         * Returns the first net node encountered during parsing with known address and
         * mask, if one exists. Otherwise, returns the first net node encountered during
         * parsing.
         *
         * @return this.representative
         */
        NetNode representative() {
            for (NetNode n : members) {
                if (!n.varAddress && !n.varMask)
                    return n;
            }
            return members.iterator().next();
        }

        /**
         * Returns the subnet members specified by the given subnet string.
         *
         * @return subnet members specified by the given subnet string.
         */
        private static Set<NetNode> members(String subnetString, Map<String,NetNode> addresses) {
            if (mSubnet.reset(subnetString).matches()) {
                final Set<NetNode> members = new LinkedHashSet<NetNode>();
                mSubMember.reset(mSubnet.group(1));
                while (mSubMember.find()) {
                    final String port = mSubMember.group(1);
                    if (addresses.containsKey(port)) {
                        members.add(addresses.get(port));
                    } else {
                        throw new IllegalArgumentException("Unrecognized port " + port + " in " + subnetString);
                    }
                }
                if (members.isEmpty()) {
                    throw new IllegalArgumentException("Subnet spec is empty: " + subnetString);
                }
                for (NetNode n1 : members) {
                    for (NetNode n2 : members) {
                        if (n1 != n2) {
                            if (!n1.varAddress && !n2.varAddress) {
                                if (n1.address == n2.address) {
                                    throw new IllegalArgumentException("Two ports on the same subnet must have distinct addresses: " + subnetString + " (" + n1.port + ".address = " + n2.port + ".address)");
                                }
                                if (!n1.varMask && !n2.varMask && n1.netid() != n2.netid()) {
                                    throw new IllegalArgumentException("Two ports on the same subnet must have the same net id: " + subnetString + " (" + n1.port + ".netid != " + n2.port + ".netid)");
                                }
                            }
                        }
                    }
                }
                return Collections.unmodifiableSet(members);
            } else {
                throw new IllegalArgumentException("Unrecognized subnet format: " + subnetString);
            }
        }

        /**
         * Returns a grouping of the given subnet members according to their group
         * representatives.
         *
         * @return a grouping of the given subnet members according to their group
         *         representatives.
         */
        private static Map<NetNode,Set<NetNode>> groups(String subnetString, Set<NetNode> members) {
            final Map<String,Set<NetNode>> byInterface = new LinkedHashMap<String,Set<NetNode>>();
            for (NetNode addr : members) {
                Set<NetNode> group = byInterface.get(addr.interfaceName);
                if (group == null) {
                    group = new LinkedHashSet<NetNode>();
                    byInterface.put(addr.interfaceName, group);
                }
                group.add(addr);

            }
            final Map<NetNode,Set<NetNode>> byRep = new LinkedHashMap<NetNode,Set<NetNode>>();
            for (Set<NetNode> group : byInterface.values()) {
                NetNode rep = null;
                for (NetNode ad : group) {
                    if (rep == null || (rep.varMask && !ad.varMask)) {
                        rep = ad;
                    } else {
                        if (!ad.varMask && rep.mask != ad.mask) {
                            throw new IllegalArgumentException("All members of a subnet with the same interface must have the same mask: " + subnetString);
                        }
                    }
                }

                byRep.put(rep, Collections.unmodifiableSet(group));
            }
            return Collections.unmodifiableMap(byRep);
        }
    }
}
