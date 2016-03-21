package splar.plugins.reasoners.sat.sat4j;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Random;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.orders.VarOrderHeap;

public class StaticVariableOrderSAT extends VarOrderHeap {

    private static final long serialVersionUID = 1L;
    private static final boolean $assertionsDisabled;
    private long nullchoice;

    private String[] varOrder;
    private Map<String,Integer> varName2IndexMap;
    private Boolean phase = false;  // false: negative first, true: positive first, null: random
    private int valueOrder[] = null;
    private int lastVar;
    private int[] order;
    protected int[] varpos;

    static {
        Class var10000;
        try {
            var10000 = Class.forName("splar.plugins.reasoners.sat.sat4j.StaticVariableOrderSAT");
        } catch (ClassNotFoundException var0) {
            throw new NoClassDefFoundError(var0.getMessage());
        }

        $assertionsDisabled = !var10000.desiredAssertionStatus();
    }

    public StaticVariableOrderSAT(String varOrder[], Boolean phase, Map<String,Integer> varName2IndexMap, String[] varIndex2NameMap) {
    	this.varOrder = varOrder;
    	this.varName2IndexMap = varName2IndexMap;
    	this.phase = phase;
    	this.valueOrder = null;
        this.lastVar = 1;
        this.order = new int[1];
        this.varpos = new int[1];
        this.nullchoice = 0L;
    }
    
    public void setPhase(boolean phase) {
    	this.phase = phase;
    }
    
    public void setValueOrder(int valueOrder[]) {
    	if ( this.valueOrder == null ) {
    		this.valueOrder = new int[valueOrder.length];
    	}
    	System.arraycopy(valueOrder, 0, this.valueOrder, 0, valueOrder.length);
    }

    /*
     * (non-Javadoc)
     *
     * @see org.sat4j.minisat.IHeuristics#init()
     */
    @Override
    public void init() {
        super.init();

        int var1 = this.lits.nVars() + 1;
        int var2 = this.lits.realnVars() + 1;
        int[] var3 = new int[var1];
        double[] var4 = new double[var1];
        int[] var5 = new int[var2];
        var3[0] = -1;
        var4[0] = -1.0D;
        var5[0] = -1;
        int var6 = 1;

        for(int var7 = 1; var6 < var1; ++var6) {
            if(!$assertionsDisabled && var6 <= 0) {
                throw new AssertionError();
            }

            if(!$assertionsDisabled && var6 > this.lits.nVars()) {
                throw new AssertionError("" + this.lits.nVars() + "/" + var6);
            }

            if(this.lits.belongsToPool(var6)) {
                var5[var7] = LiteralsUtils.neg(this.lits.getFromPool(var6));
                var3[var6] = var7++;
            }

            var4[var6] = 0.0D;
        }

        this.varpos = var3;
        this.activity = var4;
        this.order = var5;
        this.lastVar = 1;

        if ( valueOrder == null ) {
        	Random random = new Random();
	        for( int i = 0 ; i < varOrder.length ; i++ ) {
	        	int varIndex = varName2IndexMap.get(varOrder[i]);
	        	// random
	        	if ( phase == null ) {
	        		order[i+1] = ( random.nextBoolean() ) ?  LiteralsUtils.posLit(varIndex) : LiteralsUtils.negLit(varIndex);
	        	}
	        	// positive first
	        	else if (phase.booleanValue()) {
	        		order[i+1] = LiteralsUtils.posLit(varIndex);
	        	}
	        	// negative first
	        	else {
	        		order[i+1] = LiteralsUtils.negLit(varIndex);
	        	}
//        		System.out.print(varOrder[i] + ": " + ((order[i+1]%2==1) ? "false" : "true") + ", ");
	            varpos[varIndex] = i+1;
	        }
        }
        else {
        	for( int i = 0 ; i < valueOrder.length ; i++ ) {
	        	int varIndex = varName2IndexMap.get(varOrder[i]);
        		order[i+1] = (valueOrder[i] == 1) ? LiteralsUtils.posLit(varIndex) : LiteralsUtils.negLit(varIndex);
	            varpos[varIndex] = i+1;
        	}
        }
        lastVar = 1;
    }

    public int select() {
        if(!$assertionsDisabled && this.lastVar <= 0) {
            throw new AssertionError();
        } else {
            for(int var1 = this.lastVar; var1 < this.order.length; ++var1) {
                if(!$assertionsDisabled && var1 <= 0) {
                    throw new AssertionError();
                }

                if(this.lits.isUnassigned(this.order[var1])) {
                    this.lastVar = var1;
                    if(this.activity[var1] < 1.0E-4D) {
                        ++this.nullchoice;
                    }

                    return this.order[var1];
                }
            }

            return -1;
        }
    }

    public void undo(int var1) {
        if(!$assertionsDisabled && var1 <= 0) {
            throw new AssertionError();
        } else if(!$assertionsDisabled && var1 >= this.order.length) {
            throw new AssertionError();
        } else {
            int var2 = this.varpos[var1];
            if(var2 < this.lastVar) {
                this.lastVar = var2;
            }

            if(!$assertionsDisabled && this.lastVar <= 0) {
                throw new AssertionError();
            }
        }
    }

    public void updateVar(int var1) {
        if(!$assertionsDisabled && var1 <= 1) {
            throw new AssertionError();
        } else {
            int var2 = LiteralsUtils.var(var1);
            this.updateActivity(var2);

            int var3;
            for(var3 = this.varpos[var2]; var3 > 1 && this.activity[LiteralsUtils.var(this.order[var3 - 1])] < this.activity[var2]; --var3) {
                if(!$assertionsDisabled && var3 <= 1) {
                    throw new AssertionError();
                }

                int var4 = this.order[var3 - 1];
                if(!$assertionsDisabled && this.varpos[LiteralsUtils.var(var4)] != var3 - 1) {
                    throw new AssertionError();
                }

                this.varpos[LiteralsUtils.var(var4)] = var3;
                this.order[var3] = var4;
            }

            if(!$assertionsDisabled && var3 < 1) {
                throw new AssertionError();
            } else {
                this.varpos[var2] = var3;
                this.order[var3] = var1;
                if(var3 < this.lastVar) {
                    this.lastVar = var3;
                }

            }
        }
    }

    @Override
    public String toString() {
        return "Init VSIDS order with binary clause occurrences."; //$NON-NLS-1$
    }

    @Override
    public void printStat(PrintWriter var1, String var2) {
        var1.println(var2 + "non guided choices\t" + this.nullchoice);
    }
}




