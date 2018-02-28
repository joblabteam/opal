# frozen_string_literal: true

require 'opal/nodes/base'

module Opal
  module Nodes
    class ValueNode < Base
      handle :true, :false, :self, :nil

      def compile
        push type.to_s
      end

      def self.truthy_optimize?
        true
      end
    end

    class NumericNode < Base
      handle :int, :float

      children :value

      def compile
        push value.to_s
        wrap '(', ')' if recv?
      end

      def self.truthy_optimize?
        true
      end
    end

    class StringNode < Base
      handle :str

      children :value

      ESCAPE_CHARS = {
        'a' => '\\u0007',
        'e' => '\\u001b'
      }.freeze

      ESCAPE_REGEX = /(\\+)([#{ ESCAPE_CHARS.keys.join('') }])/

      def translate_escape_chars(inspect_string)
        inspect_string.gsub(ESCAPE_REGEX) do |original|
          if Regexp.last_match(1).length.even?
            original
          else
            Regexp.last_match(1).chop + ESCAPE_CHARS[Regexp.last_match(2)]
          end
        end
      end

      def compile
        string_value = value
        encoding = string_value.encoding
        should_encode = encoding != Encoding::UTF_8

        sanitized_value = string_value.inspect.gsub(/\\u\{([0-9a-f]+)\}/) do
          code_point = Regexp.last_match(1).to_i(16)
          to_utf16(code_point)
        end
        push translate_escape_chars(sanitized_value)

        if should_encode && RUBY_ENGINE != 'opal'
          push '.$force_encoding("', encoding.name, '")'
        end
      end

      # http://www.2ality.com/2013/09/javascript-unicode.html
      def to_utf16(code_point)
        ten_bits = 0b1111111111
        u = ->(code_unit) { '\\u' + code_unit.to_s(16).upcase }

        return u.call(code_point) if code_point <= 0xFFFF

        code_point -= 0x10000

        # Shift right to get to most significant 10 bits
        lead_surrogate = 0xD800 + (code_point >> 10)

        # Mask to get least significant 10 bits
        tail_surrogate = 0xDC00 + (code_point & ten_bits)

        u.call(lead_surrogate) + u.call(tail_surrogate)
      end
    end

    class SymbolNode < Base
      handle :sym

      children :value

      def compile
        push value.to_s.inspect
      end
    end

    class RegexpNode < Base
      handle :regexp

      attr_accessor :value, :flags

      # https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp
      SUPPORTED_FLAGS = /[gimuy]/

      def initialize(*)
        super
        extract_flags_and_value
      end

      def compile
        flags.select! do |flag|
          if SUPPORTED_FLAGS =~ flag
            true
          else
            compiler.warning "Skipping the '#{flag}' Regexp flag as it's not widely supported by JavaScript vendors."
            false
          end
        end

        case value.type
        when :dstr, :begin
          compile_dynamic_regexp
        when :str
          compile_static_regexp
        end
      end

      def compile_dynamic_regexp
        if flags.any?
          push 'new RegExp(', expr(value), ", '#{flags.join}')"
        else
          push 'new RegExp(', expr(value), ')'
        end
      end

      def compile_static_regexp
        value = self.value.children[0]
        case value
        when ''
          push('/(?:)/')
        when %r{\?<\w+\>}
          message = "named captures are not supported in javascript: #{value.inspect}"
          push "self.$raise(new SyntaxError('#{message}'))"
        else
          push "#{Regexp.new(value).inspect}#{flags.join}"
        end
      end

      def extract_flags_and_value
        *values, flags_sexp = *children
        self.flags = flags_sexp.children.map(&:to_s)

        self.value = case values.length
                     when 0
                       # empty regexp, we can process it inline
                       s(:str, '')
                     when 1
                       # simple plain regexp, we can put it inline
                       values[0]
                     else
                       s(:dstr, *values)
                     end

        # trimming when //x provided
        # required by parser gem, but JS doesn't support 'x' flag
        if flags.include?('x')
          parts = value.children.map do |part|
            if part.is_a?(::Opal::AST::Node) && part.type == :str
              trimmed_value = part.children[0].gsub(/\A\s*\#.*/, '').gsub(/\s/, '')
              s(:str, trimmed_value)
            else
              part
            end
          end

          self.value = value.updated(nil, parts)
          flags.delete('x')
        end

        if value.type == :str
          # Replacing \A -> ^, \z -> $, required for the parser gem
          self.value = s(:str, value.children[0].gsub('\A', '^').gsub('\z', '$'))
        end
      end

      def raw_value
        self.value = @sexp.loc.expression.source
      end
    end

    # $_ = 'foo'; call if /foo/
    # s(:if, s(:match_current_line, /foo/, true))
    class MatchCurrentLineNode < Base
      handle :match_current_line

      children :regexp

      # Here we just convert it to
      # ($_ =~ regexp)
      # and let :send node to handle it
      def compile
        gvar_sexp = s(:gvar, :$_)
        send_node = s(:send, gvar_sexp, :=~, regexp)
        push expr(send_node)
      end
    end

    class XStringNode < Base
      handle :xstr

      def compile
        should_add_semicolon = false
        has_embeded_return   = false
        returning, children  = unpack_return(self.children)
        stripped_children    = strip_empty_children(children)
        single_line          = single_line?(stripped_children)
        single_child         = stripped_children.size == 1

        if single_line
          # If it's a single line we'll try to:
          #
          # - strip empty lines
          # - remove a trailing `;`
          # - detect an embedded `return`
          # - prepend a `return` when needed
          # - append a `;` when needed
          # - warn the user not to use the semicolon in single-line x-strings

          first_child = stripped_children.shift

          if first_child.type == :str
            first_value = first_child.loc.expression.source.strip
            has_embeded_return = first_value =~ /^return\b/
          end

          if returning && !has_embeded_return
            push('return ')
          end

          last_child = stripped_children.pop || first_child
          if last_child.type == :str
            last_value = last_child.loc.expression.source.rstrip
            if (returning || expr?) && last_value[-1] == ';'
              compiler.warning(
                'Removed semicolon ending x-string expression, interpreted as unintentional',
                last_child.line,
              )
              last_value = last_value[0...-1]
            end

            should_add_semicolon = true if returning
          end

          if single_child
            push Fragment.new(last_value, scope, last_child)
          else
            compile_child(first_child)
            stripped_children.each { |c| compile_child(c) }
            if last_child.type == :str
              should_add_semicolon = false if first_child.type != :str
              push Fragment.new(last_value, scope, last_child)
            else
              compile_child(last_child)
            end
          end

        else
          # Here we leave to the user the responsibility to add
          # a return where it's due.
          children.each { |c| compile_child(c) }
        end

        wrap '(', ')' if recv?
        push ';' if should_add_semicolon
      end

      def compile_child(child)
        case child.type
        when :str
          value = child.loc.expression.source
          push Fragment.new(value, scope, child)
        when :begin, :gvar, :ivar
          push expr(child)
        else
          raise "Unsupported xstr part: #{child.type}"
        end
      end

      # Check if there's only one child or if they're all part of
      # the same line (e.g. because of interpolations)
      def single_line?(children)
        (children.size == 1) ||
          children.none? do |c|
            c.type == :str && c.loc.expression.source.end_with?("\n")
          end
      end

      # A case for manually created :js_return statement in Compiler#returns
      # Since we need to take original source of :str we have to use raw source
      # so we need to combine "return" with "raw_source"
      def unpack_return(children)
        first_child = children.first
        returning   = false

        if first_child.type == :js_return
          returning = true
          children = first_child.children
        end

        return returning, children
      end

      # Will remove empty :str lines coming from cosmetic newlines in x-strings
      #
      # @example
      #   # this will generate two additional empty
      #   # children before and after `foo()`
      #   %x{
      #     foo()
      #   }
      def strip_empty_children(children)
        start_index = 0
        end_index = children.size - 1

        while start_index <= end_index &&
              (child = children[start_index]).type == :str &&
              child.loc.expression.source.rstrip.empty?
          start_index += 1
        end

        while start_index <= end_index &&
              (child = children[end_index]).type == :str &&
              child.loc.expression.source.rstrip.empty?
          end_index -= 1
        end

        children[start_index..end_index]
      end
    end

    class DynamicStringNode < Base
      handle :dstr

      def compile
        push '""'

        children.each do |part|
          push ' + '

          if part.type == :str
            push part.children[0].inspect
          else
            push '(', expr(part), ')'
          end

          wrap '(', ')' if recv?
        end
      end
    end

    class DynamicSymbolNode < DynamicStringNode
      handle :dsym
    end

    class RangeNode < Base
      children :start, :finish

      SIMPLE_CHILDREN_TYPES = %i[int float str sym].freeze

      def compile
        if compile_inline?
          helper :range
          compile_inline
        else
          compile_range_initialize
        end
      end

      def compile_inline?
        start.type == finish.type &&
          SIMPLE_CHILDREN_TYPES.include?(start.type) &&
          SIMPLE_CHILDREN_TYPES.include?(finish.type)
      end

      def compile_inline
        raise NotImplementedError
      end

      def compile_range_initialize
        raise NotImplementedError
      end
    end

    class InclusiveRangeNode < RangeNode
      handle :irange

      def compile_inline
        push '$range(', expr(start), ', ', expr(finish), ', false)'
      end

      def compile_range_initialize
        push 'Opal.Range.$new(', expr(start), ', ', expr(finish), ', false)'
      end
    end

    class ExclusiveRangeNode < RangeNode
      handle :erange

      def compile_inline
        push '$range(', expr(start), ', ', expr(finish), ', true)'
      end

      def compile_range_initialize
        push 'Opal.Range.$new(', expr(start), ',', expr(finish), ', true)'
      end
    end

    # 0b1111r -> s(:rational, (15/1))
    # -0b1111r -> s(:rational, (-15/1))
    class RationalNode < Base
      handle :rational

      children :value

      def compile
        push "Opal.Rational.$new(#{value.numerator}, #{value.denominator})"
      end
    end

    # 0b1110i -> s(:complex, (0+14i))
    # -0b1110i -> s(:complex, (0-14i))
    class ComplexNode < Base
      handle :complex

      children :value

      def compile
        push "Opal.Complex.$new(#{value.real}, #{value.imag})"
      end
    end
  end
end
