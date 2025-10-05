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
        {iterations.map((iteration) => (
          <Card key={iteration.iteration} className={iteration.tlcResult.success ? 'bg-green-50 border-green-200' : 'bg-red-50 border-red-200'}>
            <CardHeader className="flex flex-row items-center justify-between">
              <div className="flex items-center gap-2">
                {iteration.tlcResult.success ? <CheckCircle className="h-5 w-5 text-green-600" /> : <XCircle className="h-5 w-5 text-red-600" />}
                <CardTitle className="text-lg">Iteration {iteration.iteration}</CardTitle>
              </div>
              <Badge variant={iteration.tlcResult.success ? 'default' : 'destructive'}>
                {iteration.tlcResult.success ? 'Success' : 'Failed'}
              </Badge>
            </CardHeader>
            <CardContent className="space-y-2">
              <p>States explored: <Badge variant="secondary">{iteration.tlcResult.statesExplored.toLocaleString()}</Badge></p>
              {iteration.feedback && (
                <div className="mt-2 p-2 bg-white rounded text-sm">
                  <p className="font-medium mb-1">Feedback:</p>
                  <p className="text-gray-700 font-mono">{iteration.feedback}</p>
                </div>
              )}
            </CardContent>
          </Card>
        ))}
      </CardContent>
    </Card>
  );
}
