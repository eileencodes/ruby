# frozen_string_literal: false
require 'test/unit'

class TestCvar < Test::Unit::TestCase
  def test_cvar_overtaken_by_parent_class
    error = eval <<~EORB
      class Parent
      end

      class Child < Parent
        @@cvar = 1

        def self.cvar
          @@cvar
        end
      end

      assert_equal 1, Child.cvar

      class Parent
        @@cvar = 2
      end

      assert_raise RuntimeError do
        Child.cvar
      end
    EORB

    assert_equal "class variable @@cvar of TestCvar::Child is overtaken by TestCvar::Parent", error.message
  end

  def test_cvar_overtaken_by_module
    error = eval <<~EORB
      class ParentForModule
        @@cvar = 1

        def self.cvar
          @@cvar
        end
      end

      assert_equal 1, ParentForModule.cvar

      module Mixin
        @@cvar = 2
      end

      class ParentForModule
        include Mixin
      end

      assert_raise RuntimeError do
        ParentForModule.cvar
      end
    EORB

    assert_equal "class variable @@cvar of TestCvar::ParentForModule is overtaken by TestCvar::Mixin", error.message
  end
end
