import java.nio.charset.Charset;
import java.util.*;
import java.io.DataInputStream;
import java.io.InputStreamReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;


public class Program {
    private static Charset UTF8_CHARSET = Charset.forName("UTF-8");

    public static void main(String[] args) throws IOException {
        if (args.length < 1) {
            System.err.print("Needs one argument!");
            return;
        }
        ClassFile cf;
        try (var in = Files.newInputStream(Paths.get(args[0]));
            var reader = new DataInputStream(in)) {
            cf = new ClassFile(reader);
        } catch (IOException x) {
            System.err.println(x);
            return;
        }

        var main_method = cf.methods.get("main");
        if (main_method == null)
            throw new Error("does not contain method main!");

        var code = main_method.attributes.get("Code");
        if (code == null)
            throw new Error("method does not contain code!");

        var insts = parse(code, cf);
        for (var v : insts) {
            if (v != null)
                System.err.print(v.getClass().getName() + "\n");
        }
        var graph = stackify(insts);
//         for () {

//         }
    }

    static MethodGraph stackify(Instruction[] insts) {
        var blocks = new BasicBlock[insts.length];
        var current_block = new BasicBlock();
        blocks[0] = current_block;
        var incoming_branches = new int[insts.length];
        incoming_branches[0] = 1;

        var block_begins = new ArrayList<Integer>();

        for (int i = 0; i < insts.length; i++) {
            var inst = insts[i];
            if (inst == null) continue;

            switch (inst) {
                case Return r: break;
                case Goto g: {
                    int dest = i + g.offset;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    g.destinations[0] = blocks[dest];

                    dest = i + 1;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                } break;
                case Branch br: {
                    int dest = i + br.offset;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    br.destinations[0] = blocks[dest];

                    dest = i + 1;
                    if (blocks[dest] == null) {
                        blocks[dest] = new BasicBlock();
                        block_begins.add(dest);
                    }
                    br.destinations[1] = blocks[dest];
                } break;
                default:
                    break;
            }
        }
        for (int i = 0; i < insts.length; i++) {
            var inst = insts[i];
            if (inst == null) {
                assert blocks[i] == null;
                continue;
            }


            if (i > 0 && blocks[i] != null) {
                if (current_block.terminator == null) {
                    var end = new Goto(0);
                    end.destinations[0] = blocks[i];
                    current_block.insts.add(end);
                    current_block.terminator = end;
                }
                current_block = blocks[i];
            }

            current_block.insts.add(inst);
            if (inst instanceof Terminator t) {
                for (var dest : t.destinations)
                    dest.incoming.add(current_block);
                current_block.terminator = t;
            }
        }

        Instruction last = current_block.insts.get(current_block.insts.size()-1);
        if (last instanceof Terminator t) {
            current_block.terminator = t;
        } else {
            throw new Error("WTF? " + last.getClass().getName());
        }


        resolveStack(blocks[0]);

        // Clean up unnecessary phi nodes.
        for (var inst : insts) {
            if (inst == null) continue;

            var ops = inst.ops;
            for (int i = 0; i < ops.length; i++) {
                if (ops[i] instanceof Phi p) {
                    var same = p.allTheSame();
                    if (same != null)
                        ops[i] = same;
                }
            }
        }
        return new MethodGraph(insts, blocks[0]);
    }

    static void resolveStack(BasicBlock b) {
        var stack = new ArrayList<Instruction>();
        if (b.inputs != null) {
            for (int i = 0; i < b.inputs.length; i++)
                stack.add(b.inputs[i]);
        }

        for (Instruction inst : b.insts) {
            for (int i = inst.ops.length; i-- > 0;) {
                int back = stack.size() - 1;
                inst.ops[i] = stack.get(back);
                stack.remove(back);
            }

            for (int j = 0; j < inst.result_count; j++) {
                stack.add(inst);
            }
        }
        for (var dest : b.terminator.destinations) {
            if (dest.inputs == null) {
                dest.inputs = new Phi[stack.size()];

                for (int i = 0; i < stack.size(); i++) {
                    dest.inputs[i] = new Phi(dest.incoming.size());
                }
                resolveStack(dest);
            } else {
                assert dest.inputs.length == stack.size() : "Unbalanced stack!";
            }
            int in_idx = dest.inputIndex(b);

            for (int i = 0; i < stack.size(); i++) {
                dest.inputs[i].ops[in_idx] = stack.get(i);
            }
        }
    }

    static Instruction[] parse(byte[] data, ClassFile cf) throws IOException {
        var is = new DataInputStream(new ByteArrayInputStream(data));
        var max_stack = is.readShort();
        var max_locals = is.readShort();
        var code = new byte[is.readInt()];
        is.read(code);

        var a = new Instruction[code.length];
        ConstObject[] const_pool = cf.constants;

        int idx;
        ConstObject obj;

        for (int i = 0; i < code.length; i++) {
            int opcode = ((int)code[i]) & 0xff;
            int begin = i;
            switch (opcode) {
                case 0x00: a[begin] = (new Nop()); break;
                case 0x01: a[begin] = (new Constant<Object>(null)); break;
                case 0x02: a[begin] = (new Constant<Integer>(-1)); break;
                case 0x03: a[begin] = (new Constant<Integer>(0)); break;
                case 0x04: a[begin] = (new Constant<Integer>(1)); break;
                case 0x05: a[begin] = (new Constant<Integer>(2)); break;
                case 0x06: a[begin] = (new Constant<Integer>(3)); break;
                case 0x07: a[begin] = (new Constant<Integer>(4)); break;
                case 0x08: a[begin] = (new Constant<Integer>(5)); break;
                case 0x09: a[begin] = (new Constant<Long>((long)0)); break;
                case 0x0a: a[begin] = (new Constant<Long>((long)1)); break;
                case 0x0b: a[begin] = (new Constant<Float>(0f)); break;
                case 0x0c: a[begin] = (new Constant<Float>(1f)); break;
                case 0x0d: a[begin] = (new Constant<Float>(2f)); break;
                case 0x0e: a[begin] = (new Constant<Double>(0.0)); break;
                case 0x0f: a[begin] = (new Constant<Double>(1.0)); break;
                case 0x10: a[begin] = (new Constant<Integer>((int)code[++i])); break;
                case 0x11: a[begin] = (new Constant<Short>((short)(code[++i] << 8 | code[++i]))); break;
                case 0x12: a[begin] = (new Constant((ConstantEntry) const_pool[code[++i]])); break;
                case 0x13:
                case 0x14:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new Constant((ConstantEntry) obj));
                    break;
                case 0x15: a[begin] = (new LoadLocal<Integer>(code[++i])); break;
                case 0x16: a[begin] = (new LoadLocal<Long>(code[++i])); break;
                case 0x17: a[begin] = (new LoadLocal<Float>(code[++i])); break;
                case 0x18: a[begin] = (new LoadLocal<Double>(code[++i])); break;
                case 0x19: a[begin] = (new LoadLocal<Object>(code[++i])); break;
                case 0x1a: a[begin] = (new LoadLocal<Integer>(0)); break;
                case 0x1b: a[begin] = (new LoadLocal<Integer>(1)); break;
                case 0x1c: a[begin] = (new LoadLocal<Integer>(2)); break;
                case 0x1d: a[begin] = (new LoadLocal<Integer>(3)); break;
                case 0x1e: a[begin] = (new LoadLocal<Long>(0)); break;
                case 0x1f: a[begin] = (new LoadLocal<Long>(1)); break;
                case 0x20: a[begin] = (new LoadLocal<Long>(2)); break;
                case 0x21: a[begin] = (new LoadLocal<Long>(3)); break;
                case 0x22: a[begin] = (new LoadLocal<Float>(0)); break;
                case 0x23: a[begin] = (new LoadLocal<Float>(1)); break;
                case 0x24: a[begin] = (new LoadLocal<Float>(2)); break;
                case 0x25: a[begin] = (new LoadLocal<Float>(3)); break;
                case 0x26: a[begin] = (new LoadLocal<Double>(0)); break;
                case 0x27: a[begin] = (new LoadLocal<Double>(1)); break;
                case 0x28: a[begin] = (new LoadLocal<Double>(2)); break;
                case 0x29: a[begin] = (new LoadLocal<Double>(3)); break;
                case 0x2a: a[begin] = (new LoadLocal<Object>(0)); break;
                case 0x2b: a[begin] = (new LoadLocal<Object>(1)); break;
                case 0x2c: a[begin] = (new LoadLocal<Object>(2)); break;
                case 0x2d: a[begin] = (new LoadLocal<Object>(3)); break;
                case 0x2e: a[begin] = (new LoadArray<Integer>()); break;
                case 0x2f: a[begin] = (new LoadArray<Long>()); break;
                case 0x30: a[begin] = (new LoadArray<Float>()); break;
                case 0x31: a[begin] = (new LoadArray<Double>()); break;
                case 0x32: a[begin] = (new LoadArray<Object>()); break;
                case 0x33: a[begin] = (new LoadArray<Byte>()); break;
                case 0x34: a[begin] = (new LoadArray<Character>()); break;
                case 0x35: a[begin] = (new LoadArray<Short>()); break;
                case 0x36: a[begin] = (new StoreLocal<Integer>(code[++i])); break;
                case 0x37: a[begin] = (new StoreLocal<Long>(code[++i])); break;
                case 0x38: a[begin] = (new StoreLocal<Float>(code[++i])); break;
                case 0x39: a[begin] = (new StoreLocal<Double>(code[++i])); break;
                case 0x3a: a[begin] = (new StoreLocal<Object>(code[++i])); break;
                case 0x3b: a[begin] = (new StoreLocal<Integer>(0)); break;
                case 0x3c: a[begin] = (new StoreLocal<Integer>(1)); break;
                case 0x3d: a[begin] = (new StoreLocal<Integer>(2)); break;
                case 0x3e: a[begin] = (new StoreLocal<Integer>(3)); break;
                case 0x3f: a[begin] = (new StoreLocal<Long>(0)); break;
                case 0x40: a[begin] = (new StoreLocal<Long>(1)); break;
                case 0x41: a[begin] = (new StoreLocal<Long>(2)); break;
                case 0x42: a[begin] = (new StoreLocal<Long>(3)); break;
                case 0x43: a[begin] = (new StoreLocal<Float>(0)); break;
                case 0x44: a[begin] = (new StoreLocal<Float>(1)); break;
                case 0x45: a[begin] = (new StoreLocal<Float>(2)); break;
                case 0x46: a[begin] = (new StoreLocal<Float>(3)); break;
                case 0x47: a[begin] = (new StoreLocal<Double>(0)); break;
                case 0x48: a[begin] = (new StoreLocal<Double>(1)); break;
                case 0x49: a[begin] = (new StoreLocal<Double>(2)); break;
                case 0x4a: a[begin] = (new StoreLocal<Double>(3)); break;
                case 0x4b: a[begin] = (new StoreLocal<Object>(0)); break;
                case 0x4c: a[begin] = (new StoreLocal<Object>(1)); break;
                case 0x4d: a[begin] = (new StoreLocal<Object>(2)); break;
                case 0x4e: a[begin] = (new StoreLocal<Object>(3)); break;
                case 0x4f: a[begin] = (new StoreArray<Integer>()); break;
                case 0x50: a[begin] = (new StoreArray<Long>()); break;
                case 0x51: a[begin] = (new StoreArray<Float>()); break;
                case 0x52: a[begin] = (new StoreArray<Double>()); break;
                case 0x53: a[begin] = (new StoreArray<Object>()); break;
                case 0x54: a[begin] = (new StoreArray<Byte>()); break;
                case 0x55: a[begin] = (new StoreArray<Character>()); break;
                case 0x56: a[begin] = (new StoreArray<Short>()); break;
                case 0x57:
                case 0x58:
                case 0x59:
                case 0x5a:
                case 0x5b:
                case 0x5c:
                case 0x5d:
                case 0x5e:
                case 0x5f: // swap
                case 0x60: a[begin] = (new Add<Integer>()); break;
                case 0x61: a[begin] = (new Add<Long>()); break;
                case 0x62: a[begin] = (new Add<Float>()); break;
                case 0x63: a[begin] = (new Add<Double>()); break;
                case 0x64: a[begin] = (new Sub<Integer>()); break;
                case 0x65: a[begin] = (new Sub<Long>()); break;
                case 0x66: a[begin] = (new Sub<Float>()); break;
                case 0x67: a[begin] = (new Sub<Double>()); break;
                case 0x68: a[begin] = (new Mul<Integer>()); break;
                case 0x69: a[begin] = (new Mul<Long>()); break;
                case 0x6a: a[begin] = (new Mul<Float>()); break;
                case 0x6b: a[begin] = (new Mul<Double>()); break;
                case 0x6c: a[begin] = (new Div<Integer>()); break;
                case 0x6d: a[begin] = (new Div<Long>()); break;
                case 0x6e: a[begin] = (new Div<Float>()); break;
                case 0x6f: a[begin] = (new Div<Double>()); break;
                case 0x70: a[begin] = (new Rem<Integer>()); break;
                case 0x71: a[begin] = (new Rem<Long>()); break;
                case 0x72: a[begin] = (new Rem<Float>()); break;
                case 0x73: a[begin] = (new Rem<Double>()); break;
                case 0x74: a[begin] = (new Neg<Integer>()); break;
                case 0x75: a[begin] = (new Neg<Long>()); break;
                case 0x76: a[begin] = (new Neg<Float>()); break;
                case 0x77: a[begin] = (new Neg<Double>()); break;
                case 0x78: a[begin] = (new Shl<Integer>()); break;
                case 0x79: a[begin] = (new Shl<Long>()); break;
                case 0x7a: a[begin] = (new Shr<Integer>()); break;
                case 0x7b: a[begin] = (new Shr<Long>()); break;
                case 0x7c: a[begin] = (new UShr<Integer>()); break;
                case 0x7d: a[begin] = (new UShr<Long>()); break;
                case 0x7e: a[begin] = (new And<Integer>()); break;
                case 0x7f: a[begin] = (new And<Long>()); break;
                case 0x80: a[begin] = (new Or<Integer>()); break;
                case 0x81: a[begin] = (new Or<Long>()); break;
                case 0x82: a[begin] = (new XOr<Integer>()); break;
                case 0x83: a[begin] = (new XOr<Long>()); break;
                case 0x84: a[begin] = (new IInc(code[++i], code[++i])); break;
                case 0x85: a[begin] = (new Convert<Integer, Long>()); break;
                case 0x86: a[begin] = (new Convert<Integer, Float>()); break;
                case 0x87: a[begin] = (new Convert<Integer, Double>()); break;
                case 0x88: a[begin] = (new Convert<Long, Integer>()); break;
                case 0x89: a[begin] = (new Convert<Long, Float>()); break;
                case 0x8a: a[begin] = (new Convert<Long, Double>()); break;
                case 0x8b: a[begin] = (new Convert<Float, Integer>()); break;
                case 0x8c: a[begin] = (new Convert<Float, Long>()); break;
                case 0x8d: a[begin] = (new Convert<Float, Double>()); break;
                case 0x8e: a[begin] = (new Convert<Double, Long>()); break;
                case 0x90: a[begin] = (new Convert<Double, Float>()); break;
                case 0x91: a[begin] = (new Convert<Integer, Byte>()); break;
                case 0x92: a[begin] = (new Convert<Integer, Character>()); break;
                case 0x93: a[begin] = (new Convert<Integer, Short>()); break;
                case 0x94: a[begin] = (new LCmp()); break;
                case 0x95: a[begin] = (new FCmp(false)); break;
                case 0x96: a[begin] = (new FCmp(true)); break;
                case 0x97: a[begin] = (new DCmp(false)); break;
                case 0x98: a[begin] = (new DCmp(true)); break;
                case 0x99: a[begin] = (new If(Compare.Eq, code[++i] << 8 | code[++i])); break;
                case 0x9a: a[begin] = (new If(Compare.Ne, code[++i] << 8 | code[++i])); break;
                case 0x9b: a[begin] = (new If(Compare.Lt, code[++i] << 8 | code[++i])); break;
                case 0x9c: a[begin] = (new If(Compare.Ge, code[++i] << 8 | code[++i])); break;
                case 0x9d: a[begin] = (new If(Compare.Gt, code[++i] << 8 | code[++i])); break;
                case 0x9e: a[begin] = (new If(Compare.Le, code[++i] << 8 | code[++i])); break;
                case 0x9f: a[begin] = (new IfCmp(Compare.Eq, code[++i] << 8 | code[++i])); break;
                case 0xa0: a[begin] = (new IfCmp(Compare.Ne, code[++i] << 8 | code[++i])); break;
                case 0xa1: a[begin] = (new IfCmp(Compare.Lt, code[++i] << 8 | code[++i])); break;
                case 0xa2: a[begin] = (new IfCmp(Compare.Ge, code[++i] << 8 | code[++i])); break;
                case 0xa3: a[begin] = (new IfCmp(Compare.Gt, code[++i] << 8 | code[++i])); break;
                case 0xa4: a[begin] = (new IfCmp(Compare.Le, code[++i] << 8 | code[++i])); break;
                case 0xa5: a[begin] = (new IfACmp(true, code[++i] << 8 | code[++i])); break;
                case 0xa6: a[begin] = (new IfACmp(false, code[++i] << 8 | code[++i])); break;
                case 0xa7:
                    idx = code[++i] << 8 | code[++i];
                    a[begin] = (new Goto((short) idx));
                    break;
                case 0xa8: // JSR, deprecated
                case 0xa9: // RET, deprecated
                    break;
                case 0xaa:
//                     int default_ = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
//                     int low = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
//                     int high = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
//                     // jump offsets ???
//                     a[begin] = (new TableSwitch(default_, low, high));
                    break;
                case 0xab:
//                     int default_ = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
//                     int npairs = code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i];
//                     // pairs ???
//                     a[begin] = (new LookupSwitch(default_, npairs));
                    break;
                case 0xac: a[begin] = (new Return<Integer>()); break;
                case 0xad: a[begin] = (new Return<Long>()); break;
                case 0xae: a[begin] = (new Return<Float>()); break;
                case 0xaf: a[begin] = (new Return<Double>()); break;
                case 0xb0: a[begin] = (new Return<Object>()); break;
                case 0xb1: a[begin] = (new Return<Void>()); break;
                case 0xb2:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     a[begin] = (new GetStatic((FieldReference) obj));
                    break;
                case 0xb3:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     a[begin] = (new PutStatic((FieldReference) obj));
                    break;
                case 0xb4:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new GetField((FieldReference) obj));
                    break;
                case 0xb5:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new PutField((FieldReference) obj));
                    break;
                case 0xb6:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     a[begin] = (new InvokeVirtual((MethodReference) obj));
//                     break;
//                 case 0xb7:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     a[begin] = (new InvokeSpecial((MethodReference) obj));
//                     break;
//                 case 0xb8:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     a[begin] = (new InvokeStatic((MethodReference) obj));
//                     break;
//                 case 0xb9:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     idx = code[++i];
//                     ++i;
//                     a[begin] = (new InvokeInterface((MethodReference) obj, idx));
//                     break;
//                 case 0xba:
//                     obj = const_pool[code[++i] << 8 | code[++i]];
//                     i++;
//                     i++;
//                     a[begin] = (new InvokeDynamic((MethodReference) obj));
//                     break;
                case 0xbb:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new New((ClassReference) obj));
                    break;
                case 0xbc: a[begin] = (new NewArray(code[++i])); break;
                case 0xbd:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new NewObjArray((ClassReference) obj));
                    break;
                case 0xbe: a[begin] = (new ArrayLength()); break;
                case 0xbf: a[begin] = (new Throw()); break;
                case 0xc0:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new CheckCast((ClassReference) obj));
                    break;
                case 0xc1:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    a[begin] = (new InstanceOf((ClassReference) obj));
                    break;
                case 0xc2: a[begin] = (new MonitorEnter()); break;
                case 0xc3: a[begin] = (new MonitorExit()); break;
                case 0xc4: // wide ???
                case 0xc5:
                    obj = const_pool[code[++i] << 8 | code[++i]];
                    idx = code[++i]; // dimensions
                    a[begin] = (new MultiNewArray((ClassReference) obj, idx));
                    break;
                case 0xc6: a[begin] = (new IfCheckNull(true, code[++i] << 8 | code[++i])); break;
                case 0xc7: a[begin] = (new IfCheckNull(false, code[++i] << 8 | code[++i])); break;
                case 0xc8: a[begin] = (new Goto(code[++i] << 24 | code[++i] << 16 | code[++i] << 8 | code[++i])); break;
                case 0xc9: // JSR, deprecated
                    break;
                case 0xca: // Breakpoint
                    break;
                default:
                    throw new Error("invalid opcode");
            }
        }

        return a;
    }
}


abstract class Instruction {
    Instruction ops[];
    int result_count;

    Instruction(int argc) {
        ops = new Instruction[argc];
        result_count = 1;
    }

    Instruction(int argc, int res_count) {
        ops = new Instruction[argc];
        result_count = res_count;
    }
}

class Nop extends Instruction {
    Nop() { super(0, 0); }
}

class Constant<T> extends Instruction {
    T val;
    Constant(T v) { super(0); val = v; }
    Constant(ConstantEntry<T> v) { super(0); val = v.val; }
}

class LoadLocal<T> extends Instruction {
    int index;
    LoadLocal(int i) { super(0); index = i; }
}
class StoreLocal<T> extends Instruction {
    int index;
    Instruction value;

    StoreLocal(int i) {
        super(1, 0);
        index = i;
    }
}

class LoadArray<T> extends Instruction {
    LoadArray() { super(2); }
    public Instruction array() { return ops[0]; }
    public Instruction index() { return ops[1]; }
}
class StoreArray<T> extends Instruction {
    StoreArray() { super(3, 0); }
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
class Shl<T> extends BinaryOperation {
    Shl() { }
}
class Shr<T> extends BinaryOperation {
    Shr() { }
}
class UShr<T> extends BinaryOperation {
    UShr() { }
}
class And<T> extends BinaryOperation {
    And() { }
}
class Or<T> extends BinaryOperation {
    Or() { }
}
class XOr<T> extends BinaryOperation {
    XOr() { }
}

class Neg<T> extends Instruction {
    Neg() { super(2); }
}
class LCmp<T> extends BinaryOperation {
    LCmp() { }
}
class FCmp extends BinaryOperation {
    boolean less;
    FCmp(boolean l) { less = l; }
}
class DCmp extends BinaryOperation {
    boolean less;
    DCmp(boolean l) { less = l; }
}

class GetField extends Instruction {
    FieldReference ref;
    GetField(FieldReference r) {
        super(1);
        ref = r;
    }
}
class PutField extends Instruction {
    FieldReference ref;
    PutField(FieldReference r) {
        super(2);
        ref = r;
    }
}



class New extends Instruction {
    ClassReference ref;
    New(ClassReference r) {
        super(0);
        ref = r;
    }
}
class NewArray extends Instruction {
    int primtype;
    NewArray(int p) {
        super(1);
        primtype = p;
    }
}
class NewObjArray extends Instruction {
    ClassReference ref;
    NewObjArray(ClassReference r) {
        super(1);
        ref = r;
    }
}
class ArrayLength extends Instruction {
    ArrayLength() { super(1); }
}
class Throw extends Instruction {
    Throw() { super(1); }
}
class CheckCast extends Instruction {
    ClassReference ref;
    CheckCast(ClassReference r) {
        super(1);
        ref = r;
    }
}
class InstanceOf extends Instruction {
    ClassReference ref;
    InstanceOf(ClassReference r) {
        super(1);
        ref = r;
    }
}
class MonitorEnter extends Instruction {
    MonitorEnter() { super(1, 0); }
}
class MonitorExit extends Instruction {
    MonitorExit() { super(1, 0); }
}
class MultiNewArray extends Instruction {
    ClassReference ref;

    MultiNewArray(ClassReference r, int dims) {
        super(dims);
        ref = r;
    }
}



class IInc extends Instruction {
    int index;
    int constant;

    IInc(int i, int c) {
        super(0, 0);
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
        super(operands, 0);
        destinations = new BasicBlock[dests];
    }
}

abstract class Branch extends Terminator {
    short offset;

    Branch(int operands, int o) {
        super(operands, 2);
        offset = (short) o;
    }
    public BasicBlock on_true() { return destinations[0]; }
    public BasicBlock on_false() { return destinations[1]; }
}

class If extends Branch {
    Compare comparison;

    If(Compare c, int o) {
        super(1, o);
        offset = (short) o;
        comparison = c;
    }
    public Instruction condition() { return ops[0]; }
}

class IfCmp extends Branch {
    Compare comparison;

    IfCmp(Compare c, int o) {
        super(2, o);
        comparison = c;
    }
    public Instruction lhs() { return ops[0]; }
    public Instruction rhs() { return ops[1]; }
}

class IfACmp extends Branch {
    boolean equal;

    IfACmp(boolean e, int o) {
        super(2, o);
        equal = e;
    }
    public Instruction lhs() { return ops[0]; }
    public Instruction rhs() { return ops[1]; }
}
class IfCheckNull extends Branch {
    boolean is_null;

    IfCheckNull(boolean e, int o) {
        super(1, o);
        is_null = e;
    }
    public Instruction condition() { return ops[0]; }
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

    BasicBlock() {
        incoming = new ArrayList<BasicBlock>();
        insts = new ArrayList<Instruction>();
    }

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
    Eq,
    Ne,
}



class ClassFile {
    ConstObject[] constants;
    HashMap<String, Method> methods;
    HashMap<String, Field> fields;
    HashMap<String, byte[]> attributes;

    static int ACC_PUBLIC = 0x0001; // 	Declared public; may be accessed from outside its package.
    static int ACC_FINAL = 0x0010; // 	Declared final; no subclasses allowed.
    static int ACC_SUPER = 0x0020; // 	Treat superclass methods specially when invoked by the invokespecial instruction.
    static int ACC_INTERFACE = 0x0200; // 	Is an interface, not a class.
    static int ACC_ABSTRACT = 0x0400; // 	Declared abstract; must not be instantiated.
    static int ACC_SYNTHETIC = 0x1000; // 	Declared synthetic; not present in the source code.
    static int ACC_ANNOTATION = 0x2000; // 	Declared as an annotation type.
    static int ACC_ENUM = 0x4000; // 	Declared as an enum type.
    ClassFile(DataInputStream file) throws IOException {
        // https://en.wikipedia.org/wiki/Java_class_file#Representation_in_a_C-like_programming_language
        int magic = file.readInt();
        assert magic == 0xcafebabe;

        int version = file.readInt();

        var constants = new ConstObject[file.readShort()];
        System.err.println ("#constants: " + (constants.length - 1));
        for (int i = 1; i < constants.length; i++)
            constants[i] = readConstant(file);

        short access_flags = file.readShort();
        short this_flags = file.readShort();
        short super_class = file.readShort();

        var interfaces = new ClassReference[file.readShort()];
        for (int i = 0; i < interfaces.length; i++)
            interfaces[i] = (ClassReference) constants[file.readShort()];

        fields = new HashMap();
        int fields_count = file.readShort();
        for (int i = 0; i < fields_count; i++) {
            short sub_access_flags = file.readShort();
            var name = (ConstantEntry<String>) constants[file.readShort()];
            var descriptor = (ConstantEntry<String>) constants[file.readShort()];
            var attributes = readAttributes(file, file.readShort(), constants);
            fields.put(name.val, new Field(sub_access_flags, name.val, descriptor.val, attributes));
        }

        methods = new HashMap();
        int methods_count = file.readShort();
        for (int i = 0; i < methods_count; i++) {
            short sub_access_flags = file.readShort();
            var name = (ConstantEntry<String>) constants[file.readShort()];

            var descriptor = (ConstantEntry<String>) constants[file.readShort()];
            var attributes = readAttributes(file, file.readShort(), constants);
            methods.put(name.val, new Method(sub_access_flags, name.val, descriptor.val, attributes));
        }

        attributes = readAttributes(file, file.readShort(), constants);
    }

    static HashMap<String, byte[]> readAttributes(DataInputStream file, int count, ConstObject[] constants) throws IOException {
        var res = new HashMap<String, byte[]>();
        for (int i = 0; i < count; i++) {
            var name = (ConstantEntry<String>) constants[file.readShort()];
            var data = new byte[file.readInt()];
            file.read(data);
            res.put(name.val, data);
        }
        return res;
    }

    static ConstObject readConstant(DataInputStream input) throws IOException {
        // https://en.wikipedia.org/wiki/Java_class_file#The_constant_pool
        var UTF8_CHARSET = StandardCharsets.UTF_8;
        int b = input.readByte();
        switch (b) {
            case 1:
                var buf = new byte[input.readShort()];
                input.read(buf);
                return new ConstantEntry(new String(buf, UTF8_CHARSET));
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
            default:
                throw new Error("invalid constant pool entry " + b);
        }
    }
}

interface ConstObject {}

class ConstantEntry<T> implements ConstObject {
    T val;
    ConstantEntry(T v) {
        val = v;
    }
}

class ClassReference implements ConstObject {
    short index;
    ClassReference(short i) { index = i; }
}
class StringReference implements ConstObject {
    short index;
    StringReference(short i) { index = i; }
}

class Property implements ConstObject {
    ClassReference clazz;
    NameAndType field;
    Property(short c, short n) {

    }
}
class FieldReference extends Property {
    FieldReference(short c, short n) { super(c, n); }
}
class MethodReference extends Property {
    MethodReference(short c, short n) { super(c, n); }
}
class InterfaceMethodReference extends Property {
    InterfaceMethodReference(short c, short n) { super(c, n); }
}
class NameAndType implements ConstObject {
    short name;
    short type;
    NameAndType(short n, short t) {
        name = n;
        type = t;
    }
}
class MethodHandle implements ConstObject {
    byte typedescriptor;
    short index;
    MethodHandle(byte t, short i) {
        typedescriptor = t;
        index = i;
    }
}
class MethodType implements ConstObject {
    short index;
    MethodType(short i) { index = i; }
}
class Dynamic implements ConstObject {
    int what;
    Dynamic(int i) { what = i; }
}
class Module implements ConstObject {
    short id;
    Module(short i) { id = i; }
}
class Package implements ConstObject {
    short id;
    Package(short i) { id = i; }
}


class MethodGraph {
    Instruction[] insts;
    BasicBlock entry;
    MethodGraph(Instruction[] i, BasicBlock e) {
        insts = i;
        entry = e;
    }
}


class Field {
    String name;
    String descriptor;
    HashMap<String, byte[]> attributes;

    Field(int access_flags, String n, String d, HashMap<String, byte[]> a) {
        name = n;
        descriptor = d;
        attributes = a;
    }
}
class Method {
    String name;
    String descriptor;
    HashMap<String, byte[]> attributes;

    Method(int access_flags, String n, String d, HashMap<String, byte[]> a) {
        name = n;
        descriptor = d;
        attributes = a;
    }
}
