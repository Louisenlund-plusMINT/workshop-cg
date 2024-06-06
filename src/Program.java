import java.nio.charset.Charset;
import java.util.*;
import java.io.DataInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class Program {
    private static Charset UTF8_CHARSET = Charset.forName("UTF-8");

    public static void main(String[] args) {
        if (args.length < 2) {
            System.err.print("Needs one argument!");
            return;
        }
        ClassFile cf;
        try (var in = Files.newInputStream(Paths.get(args[1]));
            var reader = new DataInputStream(in)) {
            cf = new ClassFile(reader);
        } catch (IOException x) {
            System.err.println(x);
            return;
        }

        var main_method = cf.methods.get("main");
        var code = main_method.attributes.get("code");
        var insts = (Instruction[]) parse(code).toArray();
        var graph = stackify(insts);
    }

    static MethodGraph stackify(Instruction[] insts) {
        var stack = new ArrayList<Instruction>();
        var conditions = new ArrayList<Instruction>();

        var blocks = new BasicBlock[insts.length];
        var last_block = new BasicBlock();
        blocks[0] = last_block;
        var incoming_branches = new int[insts.length];
        incoming_branches[0] = 1;

        var block_begins = new ArrayList<Integer>();

        for (int i = 0; i < insts.length; i++) {
            var inst = insts[i];
            int stack_balance = -inst.ops.length;
            switch (inst) {
                case Return r: break;
                case Goto g: {
                    int dest = i + g.offset;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    blocks[dest].incoming.add(last_block);
                    g.destinations[0] = blocks[dest];
                } break;
                case Branch br: {
                    int dest = i + br.offset;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    blocks[dest].incoming.add(last_block);
                    br.destinations[0] = blocks[dest];

                    dest = i + 1;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    blocks[dest].incoming.add(last_block);
                    br.destinations[1] = blocks[dest];
                } break;
                default:
                    stack.add(inst);
                    break;
            }
        }


//         var inputs = new Instruction[insts.length][];
//         var list = new ArrayList<Instruction>();
//         propagate(list, inputs);

        // Clean up unnecessary phi nodes.
        for (var inst : insts) {
            var ops = inst.ops;
            for (int i = 0; i < ops.length; i++) {
                if (ops[i] instanceof Phi p) {
                    var same = p.allTheSame();
                    if (same != null)
                        ops[i] = same;
                }
            }
        }

    }

    static void resolveStack(BasicBlock b, ArrayList<Instruction> stack) {
        for (Instruction inst : b.insts) {
            for (int i = inst.ops.length; i-- > 0;) {
                int back = stack.size() - 1;
                inst.ops[i] = stack.get(back);
                stack.remove(back);
            }
            stack.add(inst);
        }
        for (var dest : b.terminator.destinations) {
            if (dest.inputs == null) {
                dest.inputs = new Phi[stack.size()];


                for (int i = 0; i < stack.size(); i++) {
                    dest.inputs[i] = new Phi(dest.incoming.size());
                }
                resolveStack(dest, new ArrayList<Instruction>(Arrays.asList(dest.inputs)));
            } else {
                assert dest.inputs.length == stack.size() : "Unbalanced stack!";
            }
            int in_idx = dest.inputIndex(b);

            for (int i = 0; i < stack.size(); i++) {
                dest.inputs[i].ops[in_idx] = stack.get(i);
            }
        }
    }

    static List<Instruction> parse(byte code[]) {
        var a = new ArrayList<Instruction>();
        Constant[] const_pool;
        int idx;
        ConstObject obj;

        for (int i = 0; i < code.length; i++) {
            switch (code[i]) {
                case 0x00: a.add(new Nop()); break;
                case 0x01: a.add(new Constant<Object>(null)); break;
                case 0x02: a.add(new Constant<int>(-1)); break;
                case 0x03: a.add(new Constant<int>(0)); break;
                case 0x04: a.add(new Constant<int>(1)); break;
                case 0x05: a.add(new Constant<int>(2)); break;
                case 0x06: a.add(new Constant<int>(3)); break;
                case 0x07: a.add(new Constant<int>(4)); break;
                case 0x08: a.add(new Constant<int>(5)); break;
                case 0x09: a.add(new Constant<long>(0)); break;
                case 0x0a: a.add(new Constant<long>(1)); break;
                case 0x0b: a.add(new Constant<float>(0)); break;
                case 0x0c: a.add(new Constant<float>(1)); break;
                case 0x0d: a.add(new Constant<float>(2)); break;
                case 0x0e: a.add(new Constant<double>(0)); break;
                case 0x0f: a.add(new Constant<double>(1)); break;
                case 0x10: a.add(new Constant<int>(code[++i])); break;
                case 0x11: a.add(new Constant<short>(code[++i] << 8 | code[++i])); break;
                case 0x12: a.add((ConstantEntry) const_pool[code[++i]]); break;
                case 0x13:
                case 0x14:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new Constant((ConstantEntry) obj));
                    break;
                case 0x15: a.add(new LoadLocal<int>(code[++i])); break;
                case 0x16: a.add(new LoadLocal<long>(code[++i])); break;
                case 0x17: a.add(new LoadLocal<float>(code[++i])); break;
                case 0x18: a.add(new LoadLocal<double>(code[++i])); break;
                case 0x19: a.add(new LoadLocal<Object>(code[++i])); break;
                case 0x1a: a.add(new LoadLocal<int>(0)); break;
                case 0x1b: a.add(new LoadLocal<int>(1)); break;
                case 0x1c: a.add(new LoadLocal<int>(2)); break;
                case 0x1d: a.add(new LoadLocal<int>(3)); break;
                case 0x1e: a.add(new LoadLocal<long>(0)); break;
                case 0x1f: a.add(new LoadLocal<long>(1)); break;
                case 0x20: a.add(new LoadLocal<long>(2)); break;
                case 0x21: a.add(new LoadLocal<long>(3)); break;
                case 0x22: a.add(new LoadLocal<float>(0)); break;
                case 0x23: a.add(new LoadLocal<float>(1)); break;
                case 0x24: a.add(new LoadLocal<float>(2)); break;
                case 0x25: a.add(new LoadLocal<float>(3)); break;
                case 0x26: a.add(new LoadLocal<double>(0)); break;
                case 0x27: a.add(new LoadLocal<double>(1)); break;
                case 0x28: a.add(new LoadLocal<double>(2)); break;
                case 0x29: a.add(new LoadLocal<double>(3)); break;
                case 0x2a: a.add(new LoadLocal<Object>(0)); break;
                case 0x2b: a.add(new LoadLocal<Object>(1)); break;
                case 0x2c: a.add(new LoadLocal<Object>(2)); break;
                case 0x2d: a.add(new LoadLocal<Object>(3)); break;
                case 0x2e: a.add(new LoadArray<int>()); break;
                case 0x2f: a.add(new LoadArray<long>()); break;
                case 0x30: a.add(new LoadArray<float>()); break;
                case 0x31: a.add(new LoadArray<double>()); break;
                case 0x32: a.add(new LoadArray<Object>()); break;
                case 0x33: a.add(new LoadArray<byte>()); break;
                case 0x34: a.add(new LoadArray<char>()); break;
                case 0x35: a.add(new LoadArray<short>()); break;
                case 0x36: a.add(new StoreLocal<int>(code[++i])); break;
                case 0x37: a.add(new StoreLocal<long>(code[++i])); break;
                case 0x38: a.add(new StoreLocal<float>(code[++i])); break;
                case 0x39: a.add(new StoreLocal<double>(code[++i])); break;
                case 0x3a: a.add(new StoreLocal<Object>(code[++i])); break;
                case 0x3b: a.add(new StoreLocal<int>(0)); break;
                case 0x3c: a.add(new StoreLocal<int>(1)); break;
                case 0x3d: a.add(new StoreLocal<int>(2)); break;
                case 0x3e: a.add(new StoreLocal<int>(3)); break;
                case 0x3f: a.add(new StoreLocal<long>(0)); break;
                case 0x40: a.add(new StoreLocal<long>(1)); break;
                case 0x41: a.add(new StoreLocal<long>(2)); break;
                case 0x42: a.add(new StoreLocal<long>(3)); break;
                case 0x43: a.add(new StoreLocal<float>(0)); break;
                case 0x44: a.add(new StoreLocal<float>(1)); break;
                case 0x45: a.add(new StoreLocal<float>(2)); break;
                case 0x46: a.add(new StoreLocal<float>(3)); break;
                case 0x47: a.add(new StoreLocal<double>(0)); break;
                case 0x48: a.add(new StoreLocal<double>(1)); break;
                case 0x49: a.add(new StoreLocal<double>(2)); break;
                case 0x4a: a.add(new StoreLocal<double>(3)); break;
                case 0x4b: a.add(new StoreLocal<Object>(0)); break;
                case 0x4c: a.add(new StoreLocal<Object>(1)); break;
                case 0x4d: a.add(new StoreLocal<Object>(2)); break;
                case 0x4e: a.add(new StoreLocal<Object>(3)); break;
                case 0x4f: a.add(new StoreArray<int>()); break;
                case 0x50: a.add(new StoreArray<long>()); break;
                case 0x51: a.add(new StoreArray<float>()); break;
                case 0x52: a.add(new StoreArray<double>()); break;
                case 0x53: a.add(new StoreArray<Object>()); break;
                case 0x54: a.add(new StoreArray<byte>()); break;
                case 0x55: a.add(new StoreArray<char>()); break;
                case 0x56: a.add(new StoreArray<short>()); break;
                case 0x56: a.add(new StoreArray<short>()); break;
                case 0x57:
                case 0x58:
                case 0x59:
                case 0x5a:
                case 0x5b:
                case 0x5c:
                case 0x5d:
                case 0x5e:
                case 0x5f: // swap
                case 0x60: a.add(new Add<int>()); break;
                case 0x61: a.add(new Add<long>()); break;
                case 0x62: a.add(new Add<float>()); break;
                case 0x63: a.add(new Add<double>()); break;
                case 0x64: a.add(new Sub<int>()); break;
                case 0x65: a.add(new Sub<long>()); break;
                case 0x66: a.add(new Sub<float>()); break;
                case 0x67: a.add(new Sub<double>()); break;
                case 0x68: a.add(new Mul<int>()); break;
                case 0x69: a.add(new Mul<long>()); break;
                case 0x6a: a.add(new Mul<float>()); break;
                case 0x6b: a.add(new Mul<double>()); break;
                case 0x6c: a.add(new Div<int>()); break;
                case 0x6d: a.add(new Div<long>()); break;
                case 0x6e: a.add(new Div<float>()); break;
                case 0x6f: a.add(new Div<double>()); break;
                case 0x70: a.add(new Rem<int>()); break;
                case 0x71: a.add(new Rem<long>()); break;
                case 0x72: a.add(new Rem<float>()); break;
                case 0x73: a.add(new Rem<double>()); break;
                case 0x74: a.add(new Neg<int>()); break;
                case 0x75: a.add(new Neg<long>()); break;
                case 0x76: a.add(new Neg<float>()); break;
                case 0x77: a.add(new Neg<double>()); break;
                case 0x78: a.add(new Shl<int>()); break;
                case 0x79: a.add(new Shl<long>()); break;
                case 0x7a: a.add(new Shr<int>()); break;
                case 0x7b: a.add(new Shr<long>()); break;
                case 0x7c: a.add(new UShr<int>()); break;
                case 0x7d: a.add(new UShr<long>()); break;
                case 0x7e: a.add(new And<int>()); break;
                case 0x7f: a.add(new And<long>()); break;
                case 0x80: a.add(new Or<int>()); break;
                case 0x81: a.add(new Or<long>()); break;
                case 0x82: a.add(new XOr<int>()); break;
                case 0x83: a.add(new XOr<long>()); break;
                case 0x84: a.add(new IInc(code[++i], code[++i])); break;
                case 0x85: a.add(new Convert<int, long>()); break;
                case 0x86: a.add(new Convert<int, float>()); break;
                case 0x87: a.add(new Convert<int, double>()); break;
                case 0x88: a.add(new Convert<long, int>()); break;
                case 0x89: a.add(new Convert<long, float>()); break;
                case 0x8a: a.add(new Convert<long, double>()); break;
                case 0x8b: a.add(new Convert<float, int>()); break;
                case 0x8c: a.add(new Convert<float, long>()); break;
                case 0x8d: a.add(new Convert<float, double>()); break;
                case 0x8e: a.add(new Convert<double, int>()); break;
                case 0x8f: a.add(new Convert<double, long>()); break;
                case 0x90: a.add(new Convert<double, float>()); break;
                case 0x91: a.add(new Convert<int, byte>()); break;
                case 0x92: a.add(new Convert<int, char>()); break;
                case 0x93: a.add(new Convert<int, short>()); break;
                case 0x94: a.add(new LCmp()); break;
                case 0x95: a.add(new FCmp(false)); break;
                case 0x96: a.add(new FCmp(true)); break;
                case 0x97: a.add(new DCmp(false)); break;
                case 0x98: a.add(new DCmp(true)); break;
                case 0x99: a.add(new If(Compare.Eq, code[++i] << 8 | code[++i])); break;
                case 0x9a: a.add(new If(Compare.Ne, code[++i] << 8 | code[++i])); break;
                case 0x9b: a.add(new If(Compare.Lt, code[++i] << 8 | code[++i])); break;
                case 0x9c: a.add(new If(Compare.Ge, code[++i] << 8 | code[++i])); break;
                case 0x9d: a.add(new If(Compare.Gt, code[++i] << 8 | code[++i])); break;
                case 0x9e: a.add(new If(Compare.Le, code[++i] << 8 | code[++i])); break;
                case 0x9f: a.add(new IfCmp(Compare.Eq, code[++i] << 8 | code[++i])); break;
                case 0xa0: a.add(new IfCmp(Compare.Ne, code[++i] << 8 | code[++i])); break;
                case 0xa1: a.add(new IfCmp(Compare.Lt, code[++i] << 8 | code[++i])); break;
                case 0xa2: a.add(new IfCmp(Compare.Ge, code[++i] << 8 | code[++i])); break;
                case 0xa3: a.add(new IfCmp(Compare.Gt, code[++i] << 8 | code[++i])); break;
                case 0xa4: a.add(new IfCmp(Compare.Le, code[++i] << 8 | code[++i])); break;
                case 0xa5: a.add(new IfACmp(true, code[++i] << 8 | code[++i])); break;
                case 0xa6: a.add(new IfACmp(false, code[++i] << 8 | code[++i])); break;
                case 0xa7:
                    idx = code[++i] << 8 | code[++i];
                    a.add(new Goto((short) idx));
                    break;
                case 0xa8:
                    idx = code[++i] << 8 | code[++i];
                    a.add(new Call((short) idx)); break;
                case 0xaa:
                    int default_ = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
                    int low = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
                    int high = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
                    // jump offsets ???
                    a.add(new TableSwitch(default_, low, high));
                    break;
                case 0xab:
                    int default_ = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
                    int npairs = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
                    // pairs ???
                    a.add(new LookupSwitch(default_, npairs));
                    break;
                case 0xac: a.add(new Return<int>()); break;
                case 0xad: a.add(new Return<long>()); break;
                case 0xae: a.add(new Return<float>()); break;
                case 0xaf: a.add(new Return<double>()); break;
                case 0xb0: a.add(new Return<Object>()); break;
                case 0xb1: a.add(new Return<void>()); break;
                case 0xb2:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new GetStatic((FieldReference) obj));
                    break;
                case 0xb3:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new PutStatic((FieldReference) obj));
                    break;
                case 0xb4:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new GetField((FieldReference) obj));
                    break;
                case 0xb5:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new PutField((FieldReference) obj));
                    break;
                case 0xb6:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new InvokeVirtual((MethodReference) obj));
                    break;
                case 0xb7:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new InvokeSpecial((MethodReference) obj));
                    break;
                case 0xb8:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new InvokeStatic((MethodReference) obj));
                    break;
                case 0xb9:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    idx = code[++i];
                    ++i;
                    a.add(new InvokeInterface((MethodReference) obj, idx));
                    break;
                case 0xba:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    i++;
                    i++;
                    a.add(new InvokeDynamic((MethodReference) obj));
                    break;
                case 0xbb:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new New((ClassReference) obj));
                    break;
                case 0xbc: a.add(new NewArray(code[++i])); break;
                case 0xbd:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new NewObjArray((ClassReference) obj));
                    break;
                case 0xbe: a.add(new ArrayLength()); break;
                case 0xbf: a.add(new Throw()); break;
                case 0xc0:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new CheckCast((ClassReference) obj));
                    break;
                case 0xc1:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a.add(new InstanceOf((ClassReference) obj));
                    break;
                case 0xc2: a.add(new MonitorEnter()); break;
                case 0xc3: a.add(new MonitorExit()); break;
                case 0xc4: // wide ???
                case 0xc5:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    idx = code[++i]; // dimensions
                    a.add(new MultiNewArray((ClassReference) obj, idx));
                    break;
                case 0xc6: a.add(new IfCheckNull(true, code[++i] << 8 | code[++i])); break;
                case 0xc7: a.add(new IfCheckNull(false, code[++i] << 8 | code[++i])); break;
                case 0xc8: a.add(new Goto(code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i])); break;
                case 0xc9: a.add(new Call(code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i])); break;
                case 0xca: a.add(new Call(code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i])); break;
                default:
                    throw new Error("invalid opcode");
            }
        }

        return a;
    }
}


abstract class Instruction {
    Instruction ops[];

    Instruction(int argc) {
        ops = new int[argc];
    }
}

class Nop extends Instruction {
    Nop() { super(0); }
}

class Constant<T> extends Instruction {
    T val;
    Constant(T v) { super(0); val = v; }
}

class LoadLocal<T> extends Instruction {
    int index;
    LoadLocal(int i) { super(0); index = i; }
}
class StoreLocal<T> extends Instruction {
    int index;
    Instruction value;

    StoreLocal(int i) {
        super(1);
        index = i;
    }
}

class LoadArray<T> extends Instruction {
    LoadArray() { super(2); }
    public Instruction array() { return ops[0]; }
    public Instruction index() { return ops[1]; }
}
class StoreArray<T> extends Instruction {
    StoreArray() { super(3); }
    public Instruction array() { return ops[0]; }
    public Instruction index() { return ops[1]; }
    public Instruction val() { return ops[2]; }
}

class BinaryOperation extends Instruction {
    BinaryOperation() { super(2); }
}
class Add<T> extends BinaryOperation {
    Add() { }
}
class Sub<T> extends BinaryOperation {
    Sub() { }
}
class Mul<T> extends BinaryOperation {
    Mul() { }
}
class Div<T> extends BinaryOperation {
    Div() { }
}
class Rem<T> extends BinaryOperation {
    Rem() { }
}

class Call extends Instruction {
    int offset;

    Call(int o) {
        super(0);
        offset = o;
    }
}

class IInc extends Instruction {
    int index;
    int constant;

    IInc(int i, int c) {
        index = i;
        if (c < 128) // Signed byte
            constant = c;
        else
            constant = c - 256;
    }
}

class Convert<From, To> extends Instruction {
    Convert() {
        super(1);
    };
}



class Phi extends Instruction {
    Phi(int count) { super(count); }

    Instruction allTheSame() {
        var first = ops[0];
        for (var o : ops) {
            if (o != first)
                return null;
        }
        return first;
    }
}


abstract class Terminator extends Instruction {
    BasicBlock[] destinations;
    Terminator(int operands, int dests) {
        super(operands);
        destinations = new BasicBlock[dests];
    }
}

abstract class Branch extends Terminator {
    short offset;

    Branch(int operands, int o) {
        super(operands, 2);
        offset = o;
    }
    public BasicBlock on_true() { return destinations[0]; }
    public Instruction on_false() { return destinations[1]; }
}

class If extends Branch {
    Compare comparison;

    If(Compare c, short o) {
        super(1, o);
        offset = o;
        comparison = c;
    }
    public Instruction condition() { return ops[0]; }
}

class IfCmp extends Branch {
    Compare comparison;

    IfCmp(Compare c, short o) {
        super(2, o);
        comparison = c;
    }
    public Instruction lhs() { return ops[0]; }
    public Instruction rhs() { return ops[1]; }
}

class IfACmp extends Branch {
    boolean equal;

    IfACmp(boolean eql, short o) {
        super(2, o);
        equal = e;
    }
    public Instruction lhs() { return ops[0]; }
    public Instruction rhs() { return ops[1]; }
}

class Return<T> extends Terminator {
    Return() { super(1, 0); }
}

class Goto extends Terminator {
    int offset;
    BasicBlock dest;

    Goto(int o) {
        super(0, 1);
        offset = o;
    }
}

class BasicBlock {
    ArrayList<BasicBlock> incoming;
    ArrayList<Instruction> insts;

    // Used for construction.
    Instruction[] inputs;

    Terminator terminator;

    // PERFORMANCE Oh no!
    int inputIndex(BasicBlock inc) {
        for (int i = 0; i < incoming.size(); i++) {
            if (inc == incoming.get(i))
                return i;
        }
        return -1;
    }
}


enum Compare {
    Lt,
    Ge,
    Gt,
    Le,
}



class ClassFile {
    ConstObject[] constants;
    HashMap<String, Method> methods;
    HashMap<String, Method> fields;
    HashMap<String, byte[]> attributes;

    static int ACC_PUBLIC = 0x0001; // 	Declared public; may be accessed from outside its package.
    static int ACC_FINAL = 0x0010; // 	Declared final; no subclasses allowed.
    static int ACC_SUPER = 0x0020; // 	Treat superclass methods specially when invoked by the invokespecial instruction.
    static int ACC_INTERFACE = 0x0200; // 	Is an interface, not a class.
    static int ACC_ABSTRACT = 0x0400; // 	Declared abstract; must not be instantiated.
    static int ACC_SYNTHETIC = 0x1000; // 	Declared synthetic; not present in the source code.
    static int ACC_ANNOTATION = 0x2000; // 	Declared as an annotation type.
    static int ACC_ENUM = 0x4000; // 	Declared as an enum type.
    ClassFile(DataInputStream file) {
        // https://en.wikipedia.org/wiki/Java_class_file#Representation_in_a_C-like_programming_language
        int magic = file.readInt();
        assert magic = 0xcafebabe;

        int version = file.readInt();

        var constants = new ConstObject[file.readShort()];
        for (int i = 0; i < constant_pool_count; i++)
            constants[i] = readConstant(file);

        short access_flags = file.readShort();
        short this_flags = file.readShort();
        short super_class = file.readShort();

        var interfaces = new ClassReference[file.readShort()];
        for (int i = 0; i < interfaces.length; i++)
            interfaces[i] = (ClassReference) constants[file.readShort()];

        fields = new HashMap();
        for (int i = 0; i < fields.length; i++) {
            short access_flags = file.readShort();
            var name = (ConstObject<String>) constants[file.readShort()];
            var descriptor = (ConstObject<String>) constants[file.readShort()];
            var attributes = readAttributes(file, file.readShort(), constants);
            fields.put(name.val, new Field(access_flags, name.val, descriptor.val, attributes));
        }

        methods = new HashMap();
        for (int i = 0; i < methods.length; i++) {
            short access_flags = file.readShort();
            var name = (ConstObject<String>) constants[file.readShort()];
            var descriptor = (ConstObject<String>) constants[file.readShort()];
            var attributes = readAttributes(file, file.readShort(), constants);
            methods.put(name.val, new Method(access_flags, name.val, descriptor.val, attributes));
        }

        attributes = readAttributes(file, file.readShort(), constants);
    }

    static HashMap<String, byte[]> readAttributes(DataInputStream file, int count, ConstObject[] constants) {
        var res = new HashMap<String, byte[]>();
        for (int i = 0; i < count; i++) {
            var name = (ConstObject<String>) constants[file.readShort()];
            var data = new byte[file.readInt()];
            file.read(data);
            res.put(name.val, data);
        }
        return res;
    }

    static ConstObject readConstant(DataInputStream input) {
        // https://en.wikipedia.org/wiki/Java_class_file#The_constant_pool
        switch (input.readByte()) {
            case 1:
                var buf = new byte[input.readShort()];
                input.read(buf);
                return new ConstantEntry(new String(bytes, UTF8_CHARSET));
            case 3:
                return new ConstantEntry(input.readInt());
            case 4:
                return new ConstantEntry(input.readFloat());
            case 5:
                return new ConstantEntry(input.readLong());
            case 6:
                return new ConstantEntry(input.readDouble());
            case 7:
                return new ClassReference(input.readShort());
            case 8:
                return new StringReference(input.readShort());
            case 9:
                return new FieldReference(input.readShort(), input.readShort());
            case 10:
                return new MethodReference(input.readShort(), input.readShort());
            case 11:
                return new InterfaceMethodReference(input.readShort(), input.readShort());
            case 12:
                return new NameAndType(input.readShort(), input.readShort());
            case 15:
                return new MethodHandle(input.readByte(), input.readShort());
            case 16:
                return new MethodType(input.readShort());
            case 17:
            case 18:
                return new Dynamic(input.readInt());
            case 19:
                return new Module(input.readShort());
            case 20:
                return new Package(input.readShort());
        }
    }
}

abstract class ConstObject {}

class ConstantEntry<T> extends ConstObject {
    T val;
    ConstantEntry(T v) { val = v; }
}

class ClassReference extends ConstObject {
    short index;
    ClassReference(short i) { index = i; }
}
class StringReference extends ConstObject {
    short index;
    StringReference(short i) { index = i; }
}

class Property extends ConstObject {
    ClassReference clazz;
    NameAndType field;
}
class FieldReference extends Property {

}
class MethodReference extends Property {

}
class InterfaceMethodReference extends Property {

}
class NameAndType extends ConstObject {
    short name;
    short type;
}
class MethodHandle extends ConstObject {
    byte typedescriptor;
    short index;
}
class MethodType extends ConstObject {
    short index;
}
class Dynamic extends ConstObject {
    int what;
}
class Module extends ConstObject {
    short id;
}
class Package extends ConstObject {
    short id;
}


class MethodGraph {
    Instruction[] insts;
    BasicBlock entry;
}


class Field {
    String name;
    String descriptor;
    HashMap<String, byte[]> attributes;
}
class Method {
    String name;
    String descriptor;
    HashMap<String, byte[]> attributes;
}
