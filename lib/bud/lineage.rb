require 'pp'

class Lineage
  def initialize(bud_instance, lhs, rid)
    @froms = []
    @grouping_cols = []
    @quals = {}
    @cquals = {}
    @proj = nil
    @bud_instance = bud_instance
    @lhs = lhs
    @rule_indx = rid
    @has_body = false
  end

  def startup(ast)
    @orig_ast = ast
    if ast.first == :call and [:-@, :~, :+@].include? ast[2]
      startup(ast[1])
    else
      process_rhs(ast)
    end
  end
  
  def process_rhs(ast)
    if ast.first == :call
      fromlist(ast)
    else
      process_body(ast)
    end
  end

  def process_body(ast)
    @has_body = true
    # there is a body
    _, from, binds, ret = ast
    if from.nil?
      # bizarre tc_collections legacy; foo <= true
      return
    end
    fromlist(from)
    unless binds.nil?
      @binds = get_bindings(binds)
      exprs = get_expr(ret)
      @rets = clean_exprs(exprs)
    else
      @binds = []
      @rets = []
    end
  end

  def clean_exprs(exprs)
    bmap = make_bmap
    rets = []
    exprs.each do |r|
      if r.class == Symbol
        rets << bmap[r]
      else
        real_r = r.map do |m|
          rh = {}
          if m.class == Hash and !m[:bind].nil?
            m[:tab] = bmap[m[:bind]]
          end
          m
        end
        rets << real_r
      end
    end
    rets
  end

  def make_bmap
    bmap = {}
    if @binds.class == Symbol
      bmap[@binds] = @froms.first
    else
      @binds.each_with_index do |b, i|
        bmap[b] = @froms[i]
      end
    end
    bmap
  end

  def schemaof(tab, second)
    # unprincipled.  return the schema of tab, unless tab is a temp,
    # in which case return the schema of second.  punt if second is a temp.
    tobj = @bud_instance.tables[tab.to_sym]
    if tobj.nil?
      []
    elsif tobj.class == Bud::BudTemp
      sobj = @bud_instance.tables[second.to_sym]
      if sobj.nil? or sobj.class == Bud::BudTemp
        # no schema, or christknows
        []
      else
        (sobj.key_cols + sobj.val_cols)
      end
    else
      (tobj.key_cols + tobj.val_cols)
    end
  end

  def lhs_schema
    lhs = @bud_instance.tables[@lhs.to_sym]
    # punt on lattices
    return [] if lhs.nil?
    # this is a huge hack to get around the problem that temp tables
    # create.  they have no schemas!
    if lhs.class == Bud::BudTemp
      # arg.  well, then its schema is uniquely determined by a single body subgoal, no?
      if @froms.length == 1 or @proj == :lefts
        s = @froms.first
      elsif @proj == :rights
        s = @froms.last
      else
        #raise "hm, what is that temp's schema?? #{@lhs}"
        puts "hm, what is that temp's schema?? #{@lhs}"
        return []
      end
      stab = @bud_instance.tables[s.to_sym]
      if stab.nil? or stab.class == Bud::BudTemp
        []
      else
        (stab.key_cols + stab.val_cols)
      end
    else
      (lhs.key_cols + lhs.val_cols)
    end
  end

  def fillin(tab)
    rets = []
    rightcol = schemaof(tab, @lhs)
    schemaof(@lhs, tab).each_with_index do |c, i|
      if @grouping_cols.length == 0
        rightcol = schemaof(tab, @lhs)
        rets <<[@bud_instance, @rule_indx, c, tab, rightcol[i], nil]
      else
        break if i == @grouping_cols.length
        rets << [@bud_instance, @rule_indx, c, tab, @grouping_cols[i], :group]
      end
    end
    rets
  end

  def records
    # get the lhs schema out of the way right away.
    ls = lhs_schema
    return nil if @froms.length == 0

    rets = []
    if !@has_body
      # if a rule has no body, a unique other collection should define
      unless @froms.length == 1 or (@proj == :lefts or @proj == :rights)
        ###raise "how can you have no projection and have more than 1 table? #{@orig_ast}"
        #puts "how can you have no projection and have more than 1 table? #{@orig_ast}"
        #return
      end

      tab = @froms.first
      rets = fillin(tab)
    else
      @rets.each do |ret|
        if ret.class == Symbol 
          rets = fillin(ret)
        else
          ret.each_with_index do |r, i|
            if r.has_key? :pos and r.has_key? :tab and not r[:tab].nil?
              sname = schemaof(r[:tab], @lhs)[r[:pos]]
              rets << [@bud_instance, @rule_indx, ls[i], r[:tab], sname, nil]
            elsif r.has_key? :key
              rets <<  [@bud_instance, @rule_indx, ls[i], r[:tab], r[:key], nil]
            elsif r.has_key? :func

            end
          end
        end
      end
    end

    rets.each do |r|
      yield r
      bi, rid, lhs, tn, cn, f = r
      if @cquals[[tn, cn]]
        t, c = @cquals[[tn, cn]]  
        yield [bi, rid, lhs, t, c, :qual]
      end
    end
    
  end
  
  def to_s
    "FROMLIST: #{@froms.inspect}, quals #{@quals.inspect}, binds #{@binds.inspect}, proj #{@proj.inspect}, rets #{@rets.inspect}"
  end

  def process_proj(ast)
    if ast.nil?
      {}
    elsif ast.first == :lit
      {:lit => ast[1]}
    elsif ast.first == :call
      if ast[1].nil?
        # looks like a self.function call
        {:func => ast[2], :args => process_proj(ast[3])}
        
      elsif ast[1].first == :lvar
        # common case of a call on a variable.
        b = ast[1][1]
        if ast[2] == :[]
          #indx = ast[3][1][1]
          indx = ast[3][1]
          {:bind => b, :pos => indx}
        else
          {:bind => b, :key => ast[2]}
        end
      else
        #puts "UM I DUNNO #{ast.inspect}"
        {:func => ast}
      end
    else
      #puts "OTHER AST #{ast}"
      {:blob => ast[1]}
    end
  end

  def get_expr(ast)
    # the goal is to return all possible return expressions of a rhs code block.
    # we special-case some common expression types.
    if ast.nil?
      []
    elsif ast.first == :lvar
      [ast[1]]
    elsif ast.first == :array
      [ast[1..-1].map{|a| process_proj(a)}]
    elsif ast.first == :if or ast.first == :unless
      get_expr(ast[2]) + get_expr(ast[3])
    elsif ast.first == :block
      ret = []
      ast[1..-1].each do |node|
        ret = ret + get_expr(node)
      end
      ret
    else
      ##puts "don't grok expression #{ast}"
      []
    end
  end

  def get_bindings(ast)
    if ast.first == :args
      #ast[1..-1].map{|a| a.first}
      ast[1..-1]
      # the rest of the branches are for backwards compatibility with the old AST...
      # can probably remove.
    elsif ast.first == :lasgn
      ast[1]
    elsif ast.first == :masgn and ast[1].first == :array
      ast[1][1..-1].map{|a| get_bindings(a)}
    else
      puts "HUH bindings #{ast}"
      []
    end
  end

  def get_quals(ast)
    return if ast.nil?
    if ast.first == :hash and !ast[1].nil? #and ast[1].first == :hash
      @quals = Hash[*ast[1..-1].map{|a| a[1]}]
    end
  end

  def tab_handle(ast)
    ast
  end

  def get_grouping_col(ast)
    if ast.first == :lit
      ast[1]
    end
  end

  def get_group(ast)
    if ast.first == :arglist and ast[1].first == :array
      @grouping_cols = ast[1][1..-1].map{|g| get_grouping_col(g)}
    end
  end
  
  def handle_notin(ast)
    if ast.first == :arglist
      @froms << ast[1][2]
      if ast[2] and ast[2].first == :hash
        @quals = Hash[*ast[2][1..-1].map{|a| a[1]}] 
      end
    
    end
  end

  def fromlist(ast)
    #pp ast
    if ast[1].nil?
      @froms << tab_handle(ast[2])
    else
      froms = ast[1]
      proj = ast[2]
      if proj == :*
        # there is deeper still to go.
        fromlist(froms)
        #@froms << tab_handle(ast[3][2][1])
        @froms << tab_handle(ast[3][2])
      elsif [:group, :argagg].include? proj
        fromlist(froms)
        get_group(ast[3]) 
      elsif proj == :notin
        # special syntax here.
        @froms << tab_handle(ast[1][2])
        handle_notin(ast[3])
      elsif [:lefts, :rights, :matches, :pairs, :combos, :outer].include? proj
        @proj = proj
        fromlist(froms)
        get_quals(ast[3])
      else
        # let's assume that this is a dot-notation situation.
        if proj == :inspected
          @froms << froms[2]
        else
          @froms << "#{froms[2]}.#{proj}".to_sym
        end
        
      end
    end
    
    # canonicalize those dang quals.  we need them because they tell us about equivalence constraints
    # between lineages we know something about and lineages about which we know less.
    canonicalize_quals
  end

  def tab_assoc(col, starting=0)
    @froms[starting..-1].each_with_index do |tn, i|
      if schemaof(tn, tn).include? col
        return [tn, i]
      end
    end
    return [nil, nil]
  end

  def canonicalize_quals
    # XXX total hack.
    # need to review the bud code to see how this works in practice but for now...
    @quals.each_pair do |k, v|
      # assume k is associated with the first table with a column k... and v with whatever table after
      # that has a column v

      l,i = tab_assoc(k)
      unless i.nil?
        r,_ = tab_assoc(v, i + 1)
        @cquals[[l, k]] = [r, v]
        @cquals[[r, v]] = [l, k]
      end
    end
  end
end

