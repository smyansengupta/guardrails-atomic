'use client';

import { IterationRecord } from '@/lib/types/verification';
import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { CheckCircle, XCircle } from 'lucide-react';

interface IterationHistoryProps {
  iterations: IterationRecord[];
}

export function IterationHistory({ iterations }: IterationHistoryProps) {
  return (
    <Card className="shadow-lg bg-white">
      <CardHeader>
        <CardTitle>CEGIS Iterations</CardTitle>
      </CardHeader>
      <CardContent className="space-y-4">
        {iterations.map((iteration) => {
          // Use z3Result (current architecture) or fallback to tlcResult (legacy)
          const result = iteration.z3Result || iteration.tlcResult;
          const isSuccess = result?.success ?? false;
          const constraintsChecked = iteration.z3Result?.constraintsChecked?.length ?? 0;

          return (
            <Card key={iteration.iteration} className={isSuccess ? 'bg-green-50 border-green-200' : 'bg-red-50 border-red-200'}>
              <CardHeader className="flex flex-row items-center justify-between">
                <div className="flex items-center gap-2">
                  {isSuccess ? <CheckCircle className="h-5 w-5 text-green-600" /> : <XCircle className="h-5 w-5 text-red-600" />}
                  <CardTitle className="text-lg">Iteration {iteration.iteration}</CardTitle>
                </div>
                <Badge variant={isSuccess ? 'default' : 'destructive'}>
                  {isSuccess ? 'Success' : 'Failed'}
                </Badge>
              </CardHeader>
              <CardContent className="space-y-2">
                {/* Show Z3 constraints checked or TLC states explored */}
                {iteration.z3Result && (
                  <p>Constraints checked: <Badge variant="secondary">{constraintsChecked}</Badge></p>
                )}
                {iteration.tlcResult && (
                  <p>States explored: <Badge variant="secondary">{iteration.tlcResult.statesExplored.toLocaleString()}</Badge></p>
                )}
                {iteration.feedback && (
                  <div className="mt-2 p-2 bg-white rounded text-sm">
                    <p className="font-medium mb-1">Feedback:</p>
                    <p className="text-gray-700 font-mono whitespace-pre-wrap">{iteration.feedback}</p>
                  </div>
                )}
              </CardContent>
            </Card>
          );
        })}
      </CardContent>
    </Card>
  );
}
