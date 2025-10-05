'use client';

import { Card, CardHeader, CardTitle, CardContent } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Spinner } from '@/components/ui/spinner';
import { CheckCircle2, AlertCircle, Code, FileText, PlayCircle, Loader2 } from 'lucide-react';
import type { StreamState } from '@/lib/hooks/useVerificationStream';

interface ProgressDisplayProps {
  streamState: StreamState;
}

/**
 * Real-time progress display for CEGIS verification
 *
 * Shows:
 * - Current phase with icon
 * - Iteration progress (e.g., "2/8")
 * - Event timeline
 * - Status indicators
 */
export function ProgressDisplay({ streamState }: ProgressDisplayProps) {
  const { isStreaming, currentPhase, currentIteration, maxIterations, events, error } = streamState;

  // Get phase icon
  const getPhaseIcon = (phase: string) => {
    if (phase.includes('code') || phase.includes('Code')) {
      return <Code className="h-5 w-5" />;
    }
    if (phase.includes('TLA') || phase.includes('tla')) {
      return <FileText className="h-5 w-5" />;
    }
    if (phase.includes('TLC') || phase.includes('Running')) {
      return <PlayCircle className="h-5 w-5" />;
    }
    if (phase.includes('complete') || phase.includes('✓')) {
      return <CheckCircle2 className="h-5 w-5 text-green-600" />;
    }
    if (phase.includes('Error') || phase.includes('failed')) {
      return <AlertCircle className="h-5 w-5 text-red-600" />;
    }
    return <Loader2 className="h-5 w-5 animate-spin" />;
  };

  return (
    <Card className="shadow-lg border-blue-200 bg-blue-50">
      <CardHeader>
        <div className="flex items-center justify-between">
          <CardTitle className="text-blue-900">
            {isStreaming ? 'Verification in Progress' : 'Verification Status'}
          </CardTitle>
          {currentIteration > 0 && (
            <Badge variant="secondary">
              Iteration {currentIteration}/{maxIterations}
            </Badge>
          )}
        </div>
      </CardHeader>
      <CardContent className="space-y-4">
        {/* Current Phase */}
        <div className="flex items-center gap-3 p-3 bg-white rounded-lg">
          {getPhaseIcon(currentPhase)}
          <div className="flex-1">
            <p className="font-medium text-gray-900">{currentPhase || 'Waiting to start...'}</p>
          </div>
          {isStreaming && <Spinner />}
        </div>

        {/* Error Display */}
        {error && (
          <div className="p-3 bg-red-50 border border-red-200 rounded-lg">
            <div className="flex items-start gap-2">
              <AlertCircle className="h-5 w-5 text-red-600 mt-0.5" />
              <div>
                <p className="font-medium text-red-900">Error</p>
                <p className="text-sm text-red-700">{error}</p>
              </div>
            </div>
          </div>
        )}

        {/* Event Timeline */}
        {events.length > 0 && (
          <div className="space-y-2">
            <p className="text-sm font-medium text-gray-700">Event Timeline:</p>
            <div className="max-h-48 overflow-y-auto space-y-1 bg-white rounded-lg p-3">
              {events.map((event, index) => (
                <div
                  key={index}
                  className="flex items-start gap-2 text-xs text-gray-600 pb-2 border-b last:border-b-0"
                >
                  <span className="text-gray-400 font-mono">
                    {new Date(event.timestamp).toLocaleTimeString()}
                  </span>
                  <span className="flex-1">
                    {event.type === 'progress' && `📍 ${event.message}`}
                    {event.type === 'iteration_start' && `🔄 Started iteration ${event.iteration}`}
                    {event.type === 'code_generated' && `✨ Code generated (${event.codeLength} chars)`}
                    {event.type === 'tla_generated' && `📄 TLA+ generated`}
                    {event.type === 'tlc_start' && `▶️  TLC started`}
                    {event.type === 'tlc_complete' &&
                      `✅ TLC complete (${event.statesExplored.toLocaleString()} states, ${event.duration}ms)`}
                    {event.type === 'iteration_complete' &&
                      (event.success
                        ? `✓ Iteration ${event.iteration} succeeded`
                        : `✗ Iteration ${event.iteration} failed`)}
                    {event.type === 'verification_complete' &&
                      (event.success ? `🎉 Verification complete!` : `❌ Verification failed`)}
                    {event.type === 'error' && `❌ Error in ${event.phase}: ${event.message}`}
                  </span>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* Progress Bar (for iterations) */}
        {currentIteration > 0 && maxIterations > 0 && (
          <div className="space-y-1">
            <div className="flex justify-between text-xs text-gray-600">
              <span>Progress</span>
              <span>
                {currentIteration}/{maxIterations} iterations
              </span>
            </div>
            <div className="h-2 bg-gray-200 rounded-full overflow-hidden">
              <div
                className="h-full bg-blue-600 transition-all duration-300"
                style={{ width: `${(currentIteration / maxIterations) * 100}%` }}
              />
            </div>
          </div>
        )}
      </CardContent>
    </Card>
  );
}
