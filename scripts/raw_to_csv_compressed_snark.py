import sys
import os
import csv
import statistics

def parse_benchmark_name(bench):
    params = bench.split("/");
    assert(len(params) == 2);
    num_cons = params[0].split("-")[-1];
    op = params[1];
    return [int(num_cons), op]
                    
def parse(fname):
    res = {};
    with open(fname, 'r') as f:
        while True:
            line = f.readline();
            if not line:
                break;
            if "ProofSize" in line:
                entries = line.split(":");
                if len(entries) != 2:
                    print("ERROR: Wrong format of line" + line);
                    sys.exit()
                # Convert to KB
                size = float(entries[1][:-1].strip().split(" ")[0])/float(pow(2,10));
                [num_cons, op] = parse_benchmark_name(entries[0]);
                if not op in res:
                    res[op] = [];
                res[op].append([num_cons, size, size, size]);
            else:
                entries = list(filter(lambda x: x != "", line.split(" ")));
                if "Benchmarking" in entries:
                    idx = entries.index("Benchmarking");
                    cur_benchmark = entries[idx + 1][:-1];
                if "time:" in entries:
                    idx = entries.index("time:");
                    time = entries[idx + 3]; 
                    time_units = entries[idx + 4];
                    min_time = entries[idx + 1][1:]; 
                    assert(time_units == entries[idx + 2]);
                    max_time = entries[idx + 5];
                    assert(time_units == entries[idx + 6][:-2]);
                    if (cur_benchmark == ""):
                        print("ERROR: Problem while parsing the file, found time without benchmark name");
                        sys.exit();
                    [num_cons, op] = parse_benchmark_name(cur_benchmark);
                    if op == "Prove":
                        # Convert to seconds
                        if time_units == "ms": 
                            time = float(time)/1000;
                            min_time = float(min_time)/1000;
                            max_time = float(max_time)/1000;
                        else:
                            assert(time_units == "s");
                    else: 
                        # Convert to ms
                        if time_units == "s": 
                            time = float(time)*1000;
                            min_time = float(min_time)*1000;
                            max_time = float(max_time)*1000;
                        else:
                            assert(time_units == "ms");
                    if not op in res:
                        res[op] = [];
                    res[op].append([num_cons, time, min_time, max_time])
    return res;

def write_results_to_csv(results, csv_fname):
    fieldnames = ["Num Constraints", "Center value", "Confidence interval min", "Confidence interval max"]
    with open(csv_fname, mode = "w") as csv_file:
        writer = csv.DictWriter(csv_file, fieldnames=fieldnames);
        writer.writeheader();
        while len(results) > 0:
            [num_cons, time, min_time, max_time] =  results.pop();
            writer.writerow({
                "Num Constraints": num_cons,
                "Center value": time,
                "Confidence interval min": min_time,
                "Confidence interval max": max_time,
            });

if __name__ == "__main__":
    results = parse("compressed-snark.txt");
    write_results_to_csv(results["Prove"], "compressed-snark/prove.csv")
    write_results_to_csv(results["ProofSize"], "compressed-snark/proof-size.csv")
    write_results_to_csv(results["Verify"], "compressed-snark/verify.csv")
