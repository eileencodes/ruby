class Foo
  def initialize
    @foo = 1
  end

  def foo
    @foo
  end
end

class Bar < Foo
end

m = Foo.instance_method(:foo)
# Call iseq dump / load from our new function,
# then assign the new iseq to the method definition
m.dup
p Marshal.load Marshal.dump(m)

# Do these two lines in C
# Then assign pointer into newly allocated method def.
# Test it out with yjit and active record and see what mem implications are
# Totally unsure how to sell this upstream.
bin = RubyVM::InstructionSequence.of(m).to_binary
iseq = RubyVM::InstructionSequence.load_from_binary(bin)
puts iseq.disasm
Bar.define_method(:foo, m)
