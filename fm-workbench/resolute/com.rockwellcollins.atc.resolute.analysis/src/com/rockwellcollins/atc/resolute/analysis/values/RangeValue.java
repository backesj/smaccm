package com.rockwellcollins.atc.resolute.analysis.values;

public class RangeValue extends ResoluteValue {
    private final ResoluteValue min;
    private final ResoluteValue max;

    public RangeValue(ResoluteValue min, ResoluteValue max) {
        this.min = min;
        this.max = max;
    }

    public ResoluteValue getMin() {
        return min;
    }

    public ResoluteValue getMax() {
        return max;
    }

    @Override
    public int hashCode() {
        return min.hashCode() + max.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof RangeValue) {
            RangeValue rv = (RangeValue) obj;
            return min.equals(rv.min) && max.equals(rv.max);
        }

        return false;
    }
}
